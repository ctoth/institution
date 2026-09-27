//! Institution adapter for exact stock-flow sentences and transition traces.
//!
//! Stock-flow adds process, boundary and ledger structure to the graded
//! conservation sentences of [`crate::ConservationInstitution`].
//!
//! A signature morphism is a [`Renaming`] of carrier symbols. It may forget
//! ledgers and their projected axes. It may not forget a stock axis, flow or
//! boundary: the transition equation reads every stock row and every column,
//! so a reduct that dropped one could satisfy it where the target does not.

use std::collections::BTreeSet;
use std::error::Error as StdError;
use std::fmt;
use std::marker::PhantomData;
use std::mem::discriminant;
use std::sync::Arc;

use conservation_core::{AxisId, BalanceLaw, GradedLaw, Kind};
use conservation_stock_flow::{
    BoundaryCorrespondence, BoundaryId, BoundaryVerdict, CarrierIdentity, ExactAmounts,
    FlowConstraintVerdict, FlowId, GradedStateLaw, LedgerId, LinearFlowConstraint, OpenBalance,
    OpenBalanceVerdict, StockFlowCarrier, StockFlowError, Symbol, SymbolId, TransitionEquation,
    TransitionRecord, TransitionRecordData, TransitionTrace, TransitionVerdict, certify_nullspace,
    check_boundary_correspondence, check_graded_state_law, check_linear_flow_constraint,
    check_open_balance, check_transition_equation,
};
use conservation_trace::LawVerdict;
use institution::{Institution, Renaming, RenamingError, Vocabulary};

use crate::{KindConflict, Kinded, check_derived_kinds, kind_image, symbol_kind};

/// A completely validated stock-flow signature backed by one exact carrier.
#[derive(Clone, Debug)]
pub struct StockFlowSignature<K> {
    carrier: Arc<StockFlowCarrier<K>>,
}

impl<K: Kind> StockFlowSignature<K> {
    /// Wraps an immutable carrier whose constructor has validated its complete
    /// named matrix and ledger structure.
    #[must_use]
    pub fn new(carrier: Arc<StockFlowCarrier<K>>) -> Self {
        Self { carrier }
    }

    /// Exact carrier interpreted by models over this signature.
    #[must_use]
    pub fn carrier(&self) -> &Arc<StockFlowCarrier<K>> {
        &self.carrier
    }

    /// Canonical structural identity used for signature equality.
    #[must_use]
    pub fn identity(&self) -> &CarrierIdentity<K> {
        self.carrier.identity()
    }

    fn is_stock(&self, axis: &AxisId) -> bool {
        self.identity().internal_effects().axis_kind(axis).is_some()
    }
}

impl<K: Kind> PartialEq for StockFlowSignature<K> {
    fn eq(&self, other: &Self) -> bool {
        self.identity() == other.identity()
    }
}

impl<K: Kind> Eq for StockFlowSignature<K> {}

/// The symbols of a carrier are its stock and ledger axes, flows, boundaries
/// and ledgers; [`SymbolId`]'s variants are its symbol classes.
impl<K: Kind> Vocabulary for StockFlowSignature<K> {
    type Symbol = SymbolId;
    type Error = Error<K>;

    fn symbols(&self) -> Vec<SymbolId> {
        let identity = self.identity();
        identity
            .internal_effects()
            .axes()
            .map(Symbol::symbol_id)
            .chain(
                identity
                    .ledgers()
                    .values()
                    .map(|ledger| ledger.axis().symbol_id()),
            )
            .chain(identity.internal_effects().columns().map(Symbol::symbol_id))
            .chain(identity.boundary_effects().columns().map(Symbol::symbol_id))
            .chain(identity.ledgers().keys().map(Symbol::symbol_id))
            .collect()
    }

    fn check(renaming: &Renaming<Self>) -> Result<(), Error<K>> {
        for (from, to) in renaming.pairs() {
            if discriminant(from) != discriminant(to) {
                return Err(Error::ClassChanged {
                    source: from.clone(),
                    target: to.clone(),
                });
            }
        }
        check_derived_kinds(renaming).map_err(Error::KindConflict)?;
        let source = renaming.source();
        let target = renaming.target();

        for symbol in target.symbols() {
            let forgettable = match &symbol {
                SymbolId::Axis(axis) => !target.is_stock(axis),
                SymbolId::Flow(_) | SymbolId::Boundary(_) => false,
                SymbolId::Ledger(_) => true,
            };
            if !forgettable && renaming.preimage(&symbol).is_none() {
                return Err(Error::Forgotten(symbol));
            }
        }

        for axis in source.symbols().iter().filter_map(AxisId::named) {
            let image = image(renaming, axis)?;
            if source.is_stock(axis) != target.is_stock(image) {
                return Err(Error::AxisRoleChanged {
                    source: axis.clone(),
                    target: image.clone(),
                });
            }
        }

        let (source_internal, target_internal) = (
            source.identity().internal_effects(),
            target.identity().internal_effects(),
        );
        for flow in source_internal.columns() {
            let image_flow = image(renaming, flow)?;
            for axis in source_internal.axes() {
                if source_internal.coefficient(axis, flow)
                    != target_internal.coefficient(image(renaming, axis)?, image_flow)
                {
                    return Err(Error::IncidenceChanged {
                        column: flow.symbol_id(),
                        axis: axis.clone(),
                    });
                }
            }
        }

        let (source_boundary, target_boundary) = (
            source.identity().boundary_effects(),
            target.identity().boundary_effects(),
        );
        for boundary in source_boundary.columns() {
            let image_boundary = image(renaming, boundary)?;
            for axis in source_boundary.axes() {
                if source_boundary.coefficient(axis, boundary)
                    != target_boundary.coefficient(image(renaming, axis)?, image_boundary)
                {
                    return Err(Error::IncidenceChanged {
                        column: boundary.symbol_id(),
                        axis: axis.clone(),
                    });
                }
            }
            if source.identity().boundary_role(boundary)
                != target.identity().boundary_role(image_boundary)
            {
                return Err(Error::BoundaryRoleChanged(boundary.clone()));
            }
        }

        for (id, ledger) in source.identity().ledgers() {
            let image_ledger = &target.identity().ledgers()[image(renaming, id)?];
            if image(renaming, ledger.axis())? != image_ledger.axis() {
                return Err(Error::LedgerAxisChanged(id.clone()));
            }
            let mut boundaries = BTreeSet::new();
            for boundary in ledger.boundaries() {
                boundaries.insert(image(renaming, boundary)?.clone());
            }
            if &boundaries != image_ledger.boundaries() {
                return Err(Error::LedgerBoundariesChanged(id.clone()));
            }
        }
        Ok(())
    }
}

impl<K: Kind> Kinded for StockFlowSignature<K> {
    type Kind = K;

    fn kind_of(&self, symbol: &SymbolId) -> Option<K> {
        let identity = self.identity();
        match symbol {
            SymbolId::Axis(axis) => identity.internal_effects().axis_kind(axis).or_else(|| {
                identity
                    .ledgers()
                    .values()
                    .find(|ledger| ledger.axis() == axis)
                    .map(|ledger| ledger.kind())
            }),
            SymbolId::Flow(flow) => identity.internal_effects().column_kind(flow),
            SymbolId::Boundary(boundary) => identity.boundary_effects().column_kind(boundary),
            SymbolId::Ledger(ledger) => identity.ledgers().get(ledger).map(|ledger| ledger.kind()),
        }
    }
}

/// A typed carrier identifier, recovered from the symbol class it belongs to.
trait Named: Symbol {
    fn named(symbol: &SymbolId) -> Option<&Self>;
}

impl Named for AxisId {
    fn named(symbol: &SymbolId) -> Option<&Self> {
        if let SymbolId::Axis(id) = symbol {
            Some(id)
        } else {
            None
        }
    }
}

impl Named for FlowId {
    fn named(symbol: &SymbolId) -> Option<&Self> {
        if let SymbolId::Flow(id) = symbol {
            Some(id)
        } else {
            None
        }
    }
}

impl Named for BoundaryId {
    fn named(symbol: &SymbolId) -> Option<&Self> {
        if let SymbolId::Boundary(id) = symbol {
            Some(id)
        } else {
            None
        }
    }
}

impl Named for LedgerId {
    fn named(symbol: &SymbolId) -> Option<&Self> {
        if let SymbolId::Ledger(id) = symbol {
            Some(id)
        } else {
            None
        }
    }
}

/// The image of a source carrier symbol, in its own class.
fn image<'a, T: Named, K: Kind>(
    renaming: &'a Renaming<StockFlowSignature<K>>,
    symbol: &T,
) -> Result<&'a T, Error<K>> {
    let source = symbol.symbol_id();
    let Some(target) = renaming.image(&source) else {
        return Err(Error::Renaming(RenamingError::Unnamed(source)));
    };
    T::named(target).ok_or_else(|| Error::ClassChanged {
        source,
        target: target.clone(),
    })
}

/// The source symbol a target carrier symbol is the image of, or `None` when
/// the renaming forgets it.
fn preimage<'a, T: Named, K: Kind>(
    renaming: &'a Renaming<StockFlowSignature<K>>,
    symbol: &T,
) -> Result<Option<&'a T>, Error<K>> {
    let target = symbol.symbol_id();
    let Some(source) = renaming.preimage(&target) else {
        return Ok(None);
    };
    T::named(source)
        .map(Some)
        .ok_or_else(|| Error::ClassChanged {
            source: source.clone(),
            target,
        })
}

/// A named exact stock-flow sentence family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StockFlowSentence<K> {
    /// Per-transition stock update equation.
    Transition(TransitionEquation),
    /// Exact linear equality over settled internal flows.
    LinearFlow(LinearFlowConstraint<K>),
    /// Exact cumulative-ledger equality over mapped boundary ports.
    Boundary(BoundaryCorrespondence),
    /// Existing graded state law over projected stocks and ledgers.
    Graded(GradedStateLaw<K>),
    /// Direct open-system balance authorized by a sealed nullspace certificate.
    OpenBalance(OpenBalance<K>),
}

/// A validated exact transition trace over one stock-flow signature.
#[derive(Clone, Debug)]
pub struct StockFlowModel<K> {
    signature: StockFlowSignature<K>,
    trace: TransitionTrace<K>,
}

impl<K: Kind> StockFlowModel<K> {
    /// Wraps a trace only when its carrier is the declared signature.
    pub fn new(
        signature: StockFlowSignature<K>,
        trace: TransitionTrace<K>,
    ) -> Result<Self, Error<K>> {
        if trace.carrier().identity() != signature.identity() {
            return Err(Error::ModelSignatureMismatch);
        }
        Ok(Self { signature, trace })
    }

    /// Model signature.
    #[must_use]
    pub fn signature(&self) -> &StockFlowSignature<K> {
        &self.signature
    }

    /// Exact accepted transition trace.
    #[must_use]
    pub fn trace(&self) -> &TransitionTrace<K> {
        &self.trace
    }
}

impl<K: Kind> PartialEq for StockFlowModel<K> {
    fn eq(&self, other: &Self) -> bool {
        self.signature == other.signature && self.trace.records() == other.trace.records()
    }
}

impl<K: Kind> Eq for StockFlowModel<K> {}

/// Typed semantic evidence retained by the adapter's richer evaluation API.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StockFlowVerdict<K> {
    /// Transition-equation evidence.
    Transition(TransitionVerdict<K>),
    /// Linear-flow evidence.
    LinearFlow(FlowConstraintVerdict),
    /// Boundary-ledger evidence.
    Boundary(BoundaryVerdict),
    /// Existing graded-law evidence.
    Graded(LawVerdict<K>),
    /// Certified direct open-balance evidence.
    OpenBalance(OpenBalanceVerdict<K>),
}

impl<K: Kind> StockFlowVerdict<K> {
    /// Whether the typed verdict carries positive evidence.
    #[must_use]
    pub fn is_satisfied(&self) -> bool {
        match self {
            Self::Transition(verdict) => verdict.is_satisfied(),
            Self::LinearFlow(verdict) => verdict.is_satisfied(),
            Self::Boundary(verdict) => verdict.is_satisfied(),
            Self::Graded(verdict) => matches!(verdict, LawVerdict::Satisfied(_)),
            Self::OpenBalance(verdict) => verdict.is_satisfied(),
        }
    }
}

/// Structural or semantic adapter failure.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Error<K> {
    /// The symbol map is not a total injective renaming.
    Renaming(RenamingError<SymbolId>),
    /// A symbol was renamed into another symbol class.
    ClassChanged {
        /// The source symbol.
        source: SymbolId,
        /// Its image, of another class.
        target: SymbolId,
    },
    /// The symbol map induces no single kind map.
    KindConflict(KindConflict<SymbolId, K>),
    /// A stock axis, flow or boundary of the target is not an image.
    Forgotten(SymbolId),
    /// A stock axis was renamed to a ledger axis, or the reverse.
    AxisRoleChanged {
        /// The source axis.
        source: AxisId,
        /// Its image, of the other role.
        target: AxisId,
    },
    /// A flow or boundary column touches the image of `axis` differently.
    IncidenceChanged {
        /// The source flow or boundary.
        column: SymbolId,
        /// The source stock axis.
        axis: AxisId,
    },
    /// A boundary's image is an input where it is an output, or the reverse.
    BoundaryRoleChanged(BoundaryId),
    /// A ledger's projected axis does not go to its image's projected axis.
    LedgerAxisChanged(LedgerId),
    /// A ledger's boundaries do not go to exactly its image's boundaries.
    LedgerBoundariesChanged(LedgerId),
    /// A model trace belongs to a different carrier identity.
    ModelSignatureMismatch,
    /// Sentence, trace, or certificate validation failed in the carrier.
    Carrier(StockFlowError<K>),
}

impl<K: Kind> fmt::Display for Error<K> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Renaming(error) => write!(formatter, "invalid stock-flow renaming: {error}"),
            Self::ClassChanged { source, target } => {
                write!(formatter, "{source} is renamed to {target}")
            }
            Self::KindConflict(conflict) => write!(formatter, "{conflict}"),
            Self::Forgotten(symbol) => write!(
                formatter,
                "{symbol} is not an image, but only ledgers and their axes may be forgotten"
            ),
            Self::AxisRoleChanged { source, target } => write!(
                formatter,
                "axis {source} and its image {target} are not both stocks or both ledger axes"
            ),
            Self::IncidenceChanged { column, axis } => {
                write!(
                    formatter,
                    "{column} does not preserve its incidence on axis {axis}"
                )
            }
            Self::BoundaryRoleChanged(boundary) => {
                write!(formatter, "boundary {boundary} does not preserve its role")
            }
            Self::LedgerAxisChanged(ledger) => {
                write!(formatter, "ledger {ledger} does not preserve its axis")
            }
            Self::LedgerBoundariesChanged(ledger) => {
                write!(
                    formatter,
                    "ledger {ledger} does not preserve its boundaries"
                )
            }
            Self::ModelSignatureMismatch => {
                formatter.write_str("model trace carrier does not match its signature")
            }
            Self::Carrier(error) => write!(formatter, "stock-flow carrier error: {error}"),
        }
    }
}

impl<K: Kind> StdError for Error<K> {}

impl<K: Kind> From<StockFlowError<K>> for Error<K> {
    fn from(error: StockFlowError<K>) -> Self {
        Self::Carrier(error)
    }
}

impl<K> From<RenamingError<SymbolId>> for Error<K> {
    fn from(error: RenamingError<SymbolId>) -> Self {
        Self::Renaming(error)
    }
}

/// Institution of exact stock-flow carriers, renamings, and traces over kinds `K`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StockFlowInstitution<K>(PhantomData<fn() -> K>);

impl<K> StockFlowInstitution<K> {
    /// The institution over kinds `K`.
    #[must_use]
    pub const fn new() -> Self {
        Self(PhantomData)
    }
}

impl<K> Default for StockFlowInstitution<K> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Kind> StockFlowInstitution<K> {
    /// Evaluates a sentence while retaining its family-specific evidence.
    pub fn evaluate(
        sentence: &StockFlowSentence<K>,
        model: &StockFlowModel<K>,
    ) -> Result<StockFlowVerdict<K>, Error<K>> {
        Ok(match sentence {
            StockFlowSentence::Transition(sentence) => {
                StockFlowVerdict::Transition(check_transition_equation(sentence, model.trace())?)
            }
            StockFlowSentence::LinearFlow(sentence) => {
                StockFlowVerdict::LinearFlow(check_linear_flow_constraint(sentence, model.trace())?)
            }
            StockFlowSentence::Boundary(sentence) => {
                StockFlowVerdict::Boundary(check_boundary_correspondence(sentence, model.trace())?)
            }
            StockFlowSentence::Graded(sentence) => {
                StockFlowVerdict::Graded(check_graded_state_law(sentence, model.trace())?)
            }
            StockFlowSentence::OpenBalance(sentence) => {
                StockFlowVerdict::OpenBalance(check_open_balance(sentence, model.trace())?)
            }
        })
    }

    fn translate(
        renaming: &Renaming<StockFlowSignature<K>>,
        sentence: &StockFlowSentence<K>,
    ) -> Result<StockFlowSentence<K>, Error<K>> {
        Self::validate_source_sentence(renaming, sentence)?;
        Ok(match sentence {
            StockFlowSentence::Transition(value) => {
                StockFlowSentence::Transition(TransitionEquation::new(value.id().clone()))
            }
            StockFlowSentence::LinearFlow(value) => {
                let mut coefficients = Vec::with_capacity(value.coefficients().len());
                for (flow, coefficient) in value.coefficients() {
                    coefficients.push((image(renaming, flow)?.clone(), coefficient.clone()));
                }
                StockFlowSentence::LinearFlow(LinearFlowConstraint::new(
                    renaming.target().carrier(),
                    value.id().clone(),
                    translate_kind(renaming, value.kind())?,
                    coefficients,
                    value.expected().clone(),
                )?)
            }
            StockFlowSentence::Boundary(value) => {
                StockFlowSentence::Boundary(BoundaryCorrespondence::new(
                    value.id().clone(),
                    image(renaming, value.ledger())?.clone(),
                ))
            }
            StockFlowSentence::Graded(value) => StockFlowSentence::Graded(GradedStateLaw::new(
                value.id().clone(),
                translate_graded(renaming, value.law())?,
            )),
            StockFlowSentence::OpenBalance(value) => {
                let form = translate_form(renaming, value.certificate().law())?;
                let certificate = certify_nullspace(
                    renaming.target().carrier(),
                    form.kind(),
                    form.coefficients()
                        .map(|(axis, coefficient)| (axis.clone(), coefficient.clone())),
                )?;
                StockFlowSentence::OpenBalance(certificate.open_balance(value.id().clone()))
            }
        })
    }

    fn validate_source_sentence(
        renaming: &Renaming<StockFlowSignature<K>>,
        sentence: &StockFlowSentence<K>,
    ) -> Result<(), Error<K>> {
        let carrier = renaming.source().carrier();
        match sentence {
            StockFlowSentence::Transition(_) => Ok(()),
            StockFlowSentence::LinearFlow(value) => value.validate(carrier).map_err(Error::from),
            StockFlowSentence::Boundary(value) => {
                value.validate(carrier).map(|_| ()).map_err(Error::from)
            }
            StockFlowSentence::Graded(value) => value.validate(carrier).map_err(Error::from),
            StockFlowSentence::OpenBalance(value) => {
                if value.certificate().carrier_identity() == renaming.source().identity() {
                    Ok(())
                } else {
                    Err(Error::Carrier(StockFlowError::CarrierMismatch))
                }
            }
        }
    }

    fn reduce(
        renaming: &Renaming<StockFlowSignature<K>>,
        model: &StockFlowModel<K>,
    ) -> Result<StockFlowModel<K>, Error<K>> {
        if model.signature() != renaming.target() {
            return Err(Error::ModelSignatureMismatch);
        }
        let source = renaming.source();
        let mut records = Vec::with_capacity(model.trace().records().len());
        for record in model.trace().records() {
            let data = record.clone().into_data();
            records.push(TransitionRecord::new(
                source.carrier(),
                TransitionRecordData {
                    before: reduce_amounts(renaming, &data.before)?,
                    after: reduce_amounts(renaming, &data.after)?,
                    requested_internal: reduce_amounts(renaming, &data.requested_internal)?,
                    settled_internal: reduce_amounts(renaming, &data.settled_internal)?,
                    requested_boundary: reduce_amounts(renaming, &data.requested_boundary)?,
                    settled_boundary: reduce_amounts(renaming, &data.settled_boundary)?,
                    ledger_before: reduce_amounts(renaming, &data.ledger_before)?,
                    ledger_after: reduce_amounts(renaming, &data.ledger_after)?,
                },
            )?);
        }
        let trace = TransitionTrace::new(source.carrier().clone(), records)?;
        StockFlowModel::new(source.clone(), trace)
    }
}

/// Translates a graded law along `renaming`.
pub(crate) fn translate_graded<K: Kind>(
    renaming: &Renaming<StockFlowSignature<K>>,
    law: &GradedLaw<K>,
) -> Result<GradedLaw<K>, Error<K>> {
    Ok(GradedLaw::new(
        translate_form(renaming, law.form())?,
        law.grade(),
    ))
}

fn translate_form<K: Kind>(
    renaming: &Renaming<StockFlowSignature<K>>,
    form: &BalanceLaw<K>,
) -> Result<BalanceLaw<K>, Error<K>> {
    let mut coefficients = Vec::with_capacity(form.coefficients().len());
    for (axis, coefficient) in form.coefficients() {
        coefficients.push((image(renaming, axis)?.clone(), coefficient.clone()));
    }
    BalanceLaw::new(
        translate_kind(renaming, form.kind())?,
        coefficients,
        *form.provenance(),
    )
    .map_err(|error| Error::Carrier(StockFlowError::from(error)))
}

fn translate_kind<K: Kind>(
    renaming: &Renaming<StockFlowSignature<K>>,
    kind: K,
) -> Result<K, Error<K>> {
    kind_image(renaming, kind).ok_or(Error::Carrier(StockFlowError::UnknownKind(kind)))
}

/// Restricts target amounts to the renaming's image and renames them back,
/// each with its source symbol's kind.
fn reduce_amounts<I: Named, K: Kind>(
    renaming: &Renaming<StockFlowSignature<K>>,
    amounts: &ExactAmounts<I, K>,
) -> Result<ExactAmounts<I, K>, Error<K>> {
    let mut reduced = Vec::with_capacity(amounts.len());
    for (id, _, amount) in amounts.iter() {
        if let Some(source) = preimage(renaming, id)? {
            let kind = symbol_kind(renaming.source(), &source.symbol_id());
            reduced.push((source.clone(), kind, amount.clone()));
        }
    }
    ExactAmounts::new(reduced).map_err(Error::from)
}

impl<K: Kind> Institution for StockFlowInstitution<K> {
    type Signature = StockFlowSignature<K>;
    type SignatureMorphism = Renaming<StockFlowSignature<K>>;
    type Sentence = StockFlowSentence<K>;
    type Model = StockFlowModel<K>;
    type Error = Error<K>;

    fn source<'a>(&self, morphism: &'a Self::SignatureMorphism) -> &'a Self::Signature {
        morphism.source()
    }

    fn target<'a>(&self, morphism: &'a Self::SignatureMorphism) -> &'a Self::Signature {
        morphism.target()
    }

    fn identity(
        &self,
        signature: &Self::Signature,
    ) -> Result<Self::SignatureMorphism, Self::Error> {
        Renaming::identity(signature)
    }

    fn compose(
        &self,
        first: &Self::SignatureMorphism,
        second: &Self::SignatureMorphism,
    ) -> Result<Self::SignatureMorphism, Self::Error> {
        first.compose(second)
    }

    fn translate_sentence(
        &self,
        morphism: &Self::SignatureMorphism,
        sentence: &Self::Sentence,
    ) -> Result<Self::Sentence, Self::Error> {
        Self::translate(morphism, sentence)
    }

    fn reduct(
        &self,
        morphism: &Self::SignatureMorphism,
        model: &Self::Model,
    ) -> Result<Self::Model, Self::Error> {
        Self::reduce(morphism, model)
    }

    fn satisfies(
        &self,
        signature: &Self::Signature,
        model: &Self::Model,
        sentence: &Self::Sentence,
    ) -> Result<bool, Self::Error> {
        if model.signature() != signature {
            return Err(Error::ModelSignatureMismatch);
        }
        Ok(Self::evaluate(sentence, model)?.is_satisfied())
    }
}
