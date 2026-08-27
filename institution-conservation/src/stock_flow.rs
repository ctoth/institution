//! Institution adapter for exact stock-flow sentences and transition traces.
//!
//! The adapter is intentionally separate from [`crate::ConservationInstitution`]:
//! the existing institution continues to interpret [`conservation_core::GradedLaw`]
//! directly, while this module adds process, boundary, and ledger structure.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error as StdError;
use std::fmt;
use std::sync::Arc;

use conservation_core::{AxisId, BalanceLaw, GradedLaw, KindId};
use conservation_stock_flow::{
    BoundaryCorrespondence, BoundaryId, BoundaryVerdict, CarrierIdentity, ExactAmounts,
    FlowConstraintVerdict, FlowId, GradedStateLaw, LedgerId, LinearFlowConstraint, OpenBalance,
    OpenBalanceVerdict, StockFlowCarrier, StockFlowError, Symbol, TransitionEquation,
    TransitionRecord, TransitionRecordData, TransitionTrace, TransitionVerdict, certify_nullspace,
    check_boundary_correspondence, check_graded_state_law, check_linear_flow_constraint,
    check_open_balance, check_transition_equation,
};
use conservation_trace::LawVerdict;
use institution::Institution;

/// A completely validated stock-flow signature backed by one exact carrier.
#[derive(Clone, Debug)]
pub struct StockFlowSignature {
    carrier: Arc<StockFlowCarrier>,
}

impl StockFlowSignature {
    /// Wraps an immutable carrier whose constructor has validated its complete
    /// named matrix and ledger structure.
    #[must_use]
    pub fn new(carrier: Arc<StockFlowCarrier>) -> Self {
        Self { carrier }
    }

    /// Exact carrier interpreted by models over this signature.
    #[must_use]
    pub fn carrier(&self) -> &Arc<StockFlowCarrier> {
        &self.carrier
    }

    /// Canonical structural identity used for signature equality.
    #[must_use]
    pub fn identity(&self) -> &CarrierIdentity {
        self.carrier.identity()
    }
}

impl PartialEq for StockFlowSignature {
    fn eq(&self, other: &Self) -> bool {
        self.identity() == other.identity()
    }
}

impl Eq for StockFlowSignature {}

impl StockFlowSignature {
    fn stock_axes(&self) -> BTreeSet<AxisId> {
        self.identity().internal_effects().axes().cloned().collect()
    }

    fn axes(&self) -> BTreeSet<AxisId> {
        self.stock_axes()
            .into_iter()
            .chain(
                self.identity()
                    .ledgers()
                    .values()
                    .map(|ledger| ledger.axis().clone()),
            )
            .collect()
    }

    fn kinds(&self) -> BTreeSet<KindId> {
        self.identity()
            .internal_effects()
            .axes()
            .filter_map(|axis| self.identity().internal_effects().axis_kind(axis).cloned())
            .chain(
                self.identity()
                    .ledgers()
                    .values()
                    .map(|ledger| ledger.kind().clone()),
            )
            .collect()
    }

    fn axis_kind(&self, axis: &AxisId) -> Option<&KindId> {
        self.identity()
            .internal_effects()
            .axis_kind(axis)
            .or_else(|| {
                self.identity()
                    .ledgers()
                    .values()
                    .find(|ledger| ledger.axis() == axis)
                    .map(|ledger| ledger.kind())
            })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Bijection<T> {
    forward: BTreeMap<T, T>,
    inverse: BTreeMap<T, T>,
}

impl<T> Bijection<T>
where
    T: Clone + Ord + fmt::Debug,
{
    fn new(
        class: &str,
        source: &BTreeSet<T>,
        target: &BTreeSet<T>,
        pairs: impl IntoIterator<Item = (T, T)>,
    ) -> Result<Self, Error> {
        let mut forward = BTreeMap::new();
        let mut inverse = BTreeMap::new();
        for (from, to) in pairs {
            if !source.contains(&from) {
                return Err(Error::InvalidMorphism(format!(
                    "unknown source {class} {from:?}"
                )));
            }
            if !target.contains(&to) {
                return Err(Error::InvalidMorphism(format!(
                    "unknown target {class} {to:?}"
                )));
            }
            if forward.insert(from.clone(), to.clone()).is_some() {
                return Err(Error::InvalidMorphism(format!(
                    "duplicate source {class} {from:?}"
                )));
            }
            if inverse.insert(to.clone(), from.clone()).is_some() {
                return Err(Error::InvalidMorphism(format!(
                    "non-injective target {class} {to:?}"
                )));
            }
        }
        if forward.len() != source.len() || inverse.len() != target.len() {
            return Err(Error::InvalidMorphism(format!(
                "{class} renaming is not a total bijection"
            )));
        }
        Ok(Self { forward, inverse })
    }

    fn identity(values: &BTreeSet<T>) -> Self {
        Self {
            forward: values
                .iter()
                .cloned()
                .map(|value| (value.clone(), value))
                .collect(),
            inverse: values
                .iter()
                .cloned()
                .map(|value| (value.clone(), value))
                .collect(),
        }
    }

    fn compose(first: &Self, second: &Self) -> Self {
        let forward = first
            .forward
            .iter()
            .map(|(source, middle)| {
                (
                    source.clone(),
                    second.forward.get(middle).expect("composable maps").clone(),
                )
            })
            .collect();
        let inverse = second
            .inverse
            .iter()
            .map(|(target, middle)| {
                (
                    target.clone(),
                    first.inverse.get(middle).expect("composable maps").clone(),
                )
            })
            .collect();
        Self { forward, inverse }
    }
}

/// A structure-preserving, invertible renaming of every named carrier symbol.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StockFlowRenaming {
    source: StockFlowSignature,
    target: StockFlowSignature,
    kinds: Bijection<KindId>,
    axes: Bijection<AxisId>,
    flows: Bijection<FlowId>,
    boundaries: Bijection<BoundaryId>,
    ledgers: Bijection<LedgerId>,
}

impl StockFlowRenaming {
    /// Validates a total structural isomorphism between two stock-flow carriers.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        source: StockFlowSignature,
        target: StockFlowSignature,
        kinds: impl IntoIterator<Item = (KindId, KindId)>,
        axes: impl IntoIterator<Item = (AxisId, AxisId)>,
        flows: impl IntoIterator<Item = (FlowId, FlowId)>,
        boundaries: impl IntoIterator<Item = (BoundaryId, BoundaryId)>,
        ledgers: impl IntoIterator<Item = (LedgerId, LedgerId)>,
    ) -> Result<Self, Error> {
        let value = Self {
            kinds: Bijection::new("kind", &source.kinds(), &target.kinds(), kinds)?,
            axes: Bijection::new("axis", &source.axes(), &target.axes(), axes)?,
            flows: Bijection::new(
                "flow",
                &source
                    .identity()
                    .internal_effects()
                    .columns()
                    .cloned()
                    .collect(),
                &target
                    .identity()
                    .internal_effects()
                    .columns()
                    .cloned()
                    .collect(),
                flows,
            )?,
            boundaries: Bijection::new(
                "boundary",
                &source
                    .identity()
                    .boundary_effects()
                    .columns()
                    .cloned()
                    .collect(),
                &target
                    .identity()
                    .boundary_effects()
                    .columns()
                    .cloned()
                    .collect(),
                boundaries,
            )?,
            ledgers: Bijection::new(
                "ledger",
                &source.identity().ledgers().keys().cloned().collect(),
                &target.identity().ledgers().keys().cloned().collect(),
                ledgers,
            )?,
            source,
            target,
        };
        value.validate_structure()?;
        Ok(value)
    }

    /// Identity structural renaming.
    #[must_use]
    pub fn identity(signature: &StockFlowSignature) -> Self {
        Self {
            source: signature.clone(),
            target: signature.clone(),
            kinds: Bijection::identity(&signature.kinds()),
            axes: Bijection::identity(&signature.axes()),
            flows: Bijection::identity(
                &signature
                    .identity()
                    .internal_effects()
                    .columns()
                    .cloned()
                    .collect(),
            ),
            boundaries: Bijection::identity(
                &signature
                    .identity()
                    .boundary_effects()
                    .columns()
                    .cloned()
                    .collect(),
            ),
            ledgers: Bijection::identity(&signature.identity().ledgers().keys().cloned().collect()),
        }
    }

    /// Domain signature.
    #[must_use]
    pub fn source(&self) -> &StockFlowSignature {
        &self.source
    }

    /// Codomain signature.
    #[must_use]
    pub fn target(&self) -> &StockFlowSignature {
        &self.target
    }

    /// Covariant image of a source quantity kind.
    #[must_use]
    pub fn map_kind(&self, value: &KindId) -> Option<&KindId> {
        self.kinds.forward.get(value)
    }

    /// Covariant image of a source stock or ledger axis.
    #[must_use]
    pub fn map_axis(&self, value: &AxisId) -> Option<&AxisId> {
        self.axes.forward.get(value)
    }

    /// Covariant image of a source internal-flow channel.
    #[must_use]
    pub fn map_flow(&self, value: &FlowId) -> Option<&FlowId> {
        self.flows.forward.get(value)
    }

    /// Covariant image of a source boundary port.
    #[must_use]
    pub fn map_boundary(&self, value: &BoundaryId) -> Option<&BoundaryId> {
        self.boundaries.forward.get(value)
    }

    /// Covariant image of a source cumulative ledger.
    #[must_use]
    pub fn map_ledger(&self, value: &LedgerId) -> Option<&LedgerId> {
        self.ledgers.forward.get(value)
    }

    /// Composes two compatible renamings.
    pub fn compose(first: &Self, second: &Self) -> Result<Self, Error> {
        if first.target != second.source {
            return Err(Error::NotComposable);
        }
        Ok(Self {
            source: first.source.clone(),
            target: second.target.clone(),
            kinds: Bijection::compose(&first.kinds, &second.kinds),
            axes: Bijection::compose(&first.axes, &second.axes),
            flows: Bijection::compose(&first.flows, &second.flows),
            boundaries: Bijection::compose(&first.boundaries, &second.boundaries),
            ledgers: Bijection::compose(&first.ledgers, &second.ledgers),
        })
    }

    fn validate_structure(&self) -> Result<(), Error> {
        for source_axis in self.source.axes() {
            let target_axis = &self.axes.forward[&source_axis];
            let source_kind = self.source.axis_kind(&source_axis).expect("known axis");
            let target_kind = self.target.axis_kind(target_axis).expect("known axis");
            if self.kinds.forward[source_kind] != *target_kind {
                return Err(Error::InvalidMorphism(format!(
                    "axis kind is not preserved for {source_axis}"
                )));
            }
            if self.source.stock_axes().contains(&source_axis)
                != self.target.stock_axes().contains(target_axis)
            {
                return Err(Error::InvalidMorphism(format!(
                    "stock/ledger axis role is not preserved for {source_axis}"
                )));
            }
        }
        self.validate_matrix(false)?;
        self.validate_matrix(true)?;
        for (source_boundary, target_boundary) in &self.boundaries.forward {
            if self.source.identity().boundary_role(source_boundary)
                != self.target.identity().boundary_role(target_boundary)
            {
                return Err(Error::InvalidMorphism(format!(
                    "boundary role is not preserved for {source_boundary}"
                )));
            }
        }
        for (source_id, target_id) in &self.ledgers.forward {
            let source_ledger = &self.source.identity().ledgers()[source_id];
            let target_ledger = &self.target.identity().ledgers()[target_id];
            if self.axes.forward.get(source_ledger.axis()) != Some(target_ledger.axis())
                || self.kinds.forward.get(source_ledger.kind()) != Some(target_ledger.kind())
            {
                return Err(Error::InvalidMorphism(format!(
                    "ledger axis or kind is not preserved for {source_id}"
                )));
            }
            let mapped_boundaries = source_ledger
                .boundaries()
                .iter()
                .map(|boundary| self.boundaries.forward[boundary].clone())
                .collect::<BTreeSet<_>>();
            if &mapped_boundaries != target_ledger.boundaries() {
                return Err(Error::InvalidMorphism(format!(
                    "ledger boundary mapping is not preserved for {source_id}"
                )));
            }
        }
        Ok(())
    }

    fn validate_matrix(&self, boundary: bool) -> Result<(), Error> {
        if boundary {
            let source = self.source.identity().boundary_effects();
            let target = self.target.identity().boundary_effects();
            for source_column in source.columns() {
                let target_column = &self.boundaries.forward[source_column];
                if self.kinds.forward[source.column_kind(source_column).expect("known column")]
                    != *target.column_kind(target_column).expect("known column")
                {
                    return Err(Error::InvalidMorphism(format!(
                        "boundary kind is not preserved for {source_column}"
                    )));
                }
                for source_axis in source.axes() {
                    let target_axis = &self.axes.forward[source_axis];
                    if source.coefficient(source_axis, source_column)
                        != target.coefficient(target_axis, target_column)
                    {
                        return Err(Error::InvalidMorphism(format!(
                            "boundary incidence is not preserved for {source_column}"
                        )));
                    }
                }
            }
        } else {
            let source = self.source.identity().internal_effects();
            let target = self.target.identity().internal_effects();
            for source_column in source.columns() {
                let target_column = &self.flows.forward[source_column];
                if self.kinds.forward[source.column_kind(source_column).expect("known column")]
                    != *target.column_kind(target_column).expect("known column")
                {
                    return Err(Error::InvalidMorphism(format!(
                        "flow kind is not preserved for {source_column}"
                    )));
                }
                for source_axis in source.axes() {
                    let target_axis = &self.axes.forward[source_axis];
                    if source.coefficient(source_axis, source_column)
                        != target.coefficient(target_axis, target_column)
                    {
                        return Err(Error::InvalidMorphism(format!(
                            "internal incidence is not preserved for {source_column}"
                        )));
                    }
                }
            }
        }
        Ok(())
    }
}

/// A named exact stock-flow sentence family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StockFlowSentence {
    /// Per-transition stock update equation.
    Transition(TransitionEquation),
    /// Exact linear equality over settled internal flows.
    LinearFlow(LinearFlowConstraint),
    /// Exact cumulative-ledger equality over mapped boundary ports.
    Boundary(BoundaryCorrespondence),
    /// Existing graded state law over projected stocks and ledgers.
    Graded(GradedStateLaw),
    /// Direct open-system balance authorized by a sealed nullspace certificate.
    OpenBalance(OpenBalance),
}

/// A validated exact transition trace over one stock-flow signature.
#[derive(Clone, Debug)]
pub struct StockFlowModel {
    signature: StockFlowSignature,
    trace: TransitionTrace,
}

impl StockFlowModel {
    /// Wraps a trace only when its carrier is the declared signature.
    pub fn new(signature: StockFlowSignature, trace: TransitionTrace) -> Result<Self, Error> {
        if trace.carrier().identity() != signature.identity() {
            return Err(Error::ModelSignatureMismatch);
        }
        Ok(Self { signature, trace })
    }

    /// Model signature.
    #[must_use]
    pub fn signature(&self) -> &StockFlowSignature {
        &self.signature
    }

    /// Exact accepted transition trace.
    #[must_use]
    pub fn trace(&self) -> &TransitionTrace {
        &self.trace
    }
}

impl PartialEq for StockFlowModel {
    fn eq(&self, other: &Self) -> bool {
        self.signature == other.signature && self.trace.records() == other.trace.records()
    }
}

impl Eq for StockFlowModel {}

/// Typed semantic evidence retained by the adapter's richer evaluation API.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StockFlowVerdict {
    /// Transition-equation evidence.
    Transition(TransitionVerdict),
    /// Linear-flow evidence.
    LinearFlow(FlowConstraintVerdict),
    /// Boundary-ledger evidence.
    Boundary(BoundaryVerdict),
    /// Existing graded-law evidence.
    Graded(LawVerdict),
    /// Certified direct open-balance evidence.
    OpenBalance(OpenBalanceVerdict),
}

impl StockFlowVerdict {
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
pub enum Error {
    /// A proposed symbol map does not preserve complete carrier structure.
    InvalidMorphism(String),
    /// The two morphisms do not share their middle signature.
    NotComposable,
    /// A model trace belongs to a different carrier identity.
    ModelSignatureMismatch,
    /// Sentence, trace, or certificate validation failed in the carrier.
    Carrier(StockFlowError),
}

impl fmt::Display for Error {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidMorphism(message) => {
                write!(formatter, "invalid stock-flow morphism: {message}")
            }
            Self::NotComposable => formatter.write_str("stock-flow morphisms are not composable"),
            Self::ModelSignatureMismatch => {
                formatter.write_str("model trace carrier does not match its signature")
            }
            Self::Carrier(error) => write!(formatter, "stock-flow carrier error: {error}"),
        }
    }
}

impl StdError for Error {}

impl From<StockFlowError> for Error {
    fn from(error: StockFlowError) -> Self {
        Self::Carrier(error)
    }
}

/// Institution of exact stock-flow carriers, structural renamings, and traces.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct StockFlowInstitution;

impl StockFlowInstitution {
    /// Evaluates a sentence while retaining its family-specific evidence.
    pub fn evaluate(
        sentence: &StockFlowSentence,
        model: &StockFlowModel,
    ) -> Result<StockFlowVerdict, Error> {
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
        morphism: &StockFlowRenaming,
        sentence: &StockFlowSentence,
    ) -> Result<StockFlowSentence, Error> {
        Self::validate_source_sentence(morphism, sentence)?;
        Ok(match sentence {
            StockFlowSentence::Transition(value) => {
                StockFlowSentence::Transition(TransitionEquation::new(value.id().clone()))
            }
            StockFlowSentence::LinearFlow(value) => {
                StockFlowSentence::LinearFlow(LinearFlowConstraint::new(
                    morphism.target().carrier(),
                    value.id().clone(),
                    morphism.kinds.forward[value.kind()].clone(),
                    value.coefficients().iter().map(|(flow, coefficient)| {
                        (morphism.flows.forward[flow].clone(), coefficient.clone())
                    }),
                    value.expected().clone(),
                )?)
            }
            StockFlowSentence::Boundary(value) => {
                StockFlowSentence::Boundary(BoundaryCorrespondence::new(
                    value.id().clone(),
                    morphism.ledgers.forward[value.ledger()].clone(),
                ))
            }
            StockFlowSentence::Graded(value) => {
                let form = value.law().form();
                let renamed = BalanceLaw::new(
                    morphism.kinds.forward[form.kind()].clone(),
                    form.coefficients().map(|(axis, coefficient)| {
                        (morphism.axes.forward[axis].clone(), coefficient.clone())
                    }),
                    *form.provenance(),
                )
                .map_err(StockFlowError::from)?;
                StockFlowSentence::Graded(GradedStateLaw::new(
                    value.id().clone(),
                    GradedLaw::new(renamed, value.law().grade()),
                ))
            }
            StockFlowSentence::OpenBalance(value) => {
                let certificate = value.certificate();
                let renamed = certify_nullspace(
                    morphism.target().carrier(),
                    morphism.kinds.forward[certificate.law().kind()].clone(),
                    certificate.law().coefficients().map(|(axis, coefficient)| {
                        (morphism.axes.forward[axis].clone(), coefficient.clone())
                    }),
                )?;
                StockFlowSentence::OpenBalance(renamed.open_balance(value.id().clone()))
            }
        })
    }

    fn validate_source_sentence(
        morphism: &StockFlowRenaming,
        sentence: &StockFlowSentence,
    ) -> Result<(), Error> {
        match sentence {
            StockFlowSentence::Transition(_) => Ok(()),
            StockFlowSentence::LinearFlow(value) => value
                .validate(morphism.source().carrier())
                .map_err(Error::from),
            StockFlowSentence::Boundary(value) => value
                .validate(morphism.source().carrier())
                .map(|_| ())
                .map_err(Error::from),
            StockFlowSentence::Graded(value) => value
                .validate(morphism.source().carrier())
                .map_err(Error::from),
            StockFlowSentence::OpenBalance(value) => {
                if value.certificate().carrier_identity() == morphism.source().identity() {
                    Ok(())
                } else {
                    Err(Error::Carrier(StockFlowError::CarrierMismatch))
                }
            }
        }
    }

    fn reduce(
        morphism: &StockFlowRenaming,
        model: &StockFlowModel,
    ) -> Result<StockFlowModel, Error> {
        if model.signature != morphism.target {
            return Err(Error::ModelSignatureMismatch);
        }
        let records = model
            .trace
            .records()
            .iter()
            .map(|record| {
                let data = record.clone().into_data();
                TransitionRecord::new(
                    morphism.source().carrier(),
                    TransitionRecordData {
                        before: remap_amounts(
                            data.before,
                            &morphism.axes.inverse,
                            &morphism.kinds.inverse,
                        )?,
                        after: remap_amounts(
                            data.after,
                            &morphism.axes.inverse,
                            &morphism.kinds.inverse,
                        )?,
                        requested_internal: remap_amounts(
                            data.requested_internal,
                            &morphism.flows.inverse,
                            &morphism.kinds.inverse,
                        )?,
                        settled_internal: remap_amounts(
                            data.settled_internal,
                            &morphism.flows.inverse,
                            &morphism.kinds.inverse,
                        )?,
                        requested_boundary: remap_amounts(
                            data.requested_boundary,
                            &morphism.boundaries.inverse,
                            &morphism.kinds.inverse,
                        )?,
                        settled_boundary: remap_amounts(
                            data.settled_boundary,
                            &morphism.boundaries.inverse,
                            &morphism.kinds.inverse,
                        )?,
                        ledger_before: remap_amounts(
                            data.ledger_before,
                            &morphism.ledgers.inverse,
                            &morphism.kinds.inverse,
                        )?,
                        ledger_after: remap_amounts(
                            data.ledger_after,
                            &morphism.ledgers.inverse,
                            &morphism.kinds.inverse,
                        )?,
                    },
                )
                .map_err(Error::from)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let trace = TransitionTrace::new(morphism.source().carrier().clone(), records)?;
        StockFlowModel::new(morphism.source().clone(), trace)
    }
}

impl Institution for StockFlowInstitution {
    type Signature = StockFlowSignature;
    type SignatureMorphism = StockFlowRenaming;
    type Sentence = StockFlowSentence;
    type Model = StockFlowModel;
    type Error = Error;

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
        Ok(StockFlowRenaming::identity(signature))
    }

    fn compose(
        &self,
        first: &Self::SignatureMorphism,
        second: &Self::SignatureMorphism,
    ) -> Result<Self::SignatureMorphism, Self::Error> {
        StockFlowRenaming::compose(first, second)
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

fn remap_amounts<Source, Target>(
    amounts: ExactAmounts<Source>,
    ids: &BTreeMap<Source, Target>,
    kinds: &BTreeMap<KindId, KindId>,
) -> Result<ExactAmounts<Target>, Error>
where
    Source: Symbol,
    Target: Symbol,
{
    ExactAmounts::new(
        amounts
            .iter()
            .map(|(id, kind, amount)| (ids[id].clone(), kinds[kind].clone(), amount.clone())),
    )
    .map_err(Error::from)
}
