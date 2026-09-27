#![forbid(unsafe_code)]

//! The institution of graded conservation sentences and finite traces.
//!
//! Sentences are [`GradedLaw`]s: one exact linear form read as an invariant
//! balance, a nonnegativity constraint, or a nondecreasing (dissipation)
//! constraint. Translation renames the form and preserves the grade, so one
//! satisfaction condition covers every grade.
//!
//! Signature morphisms are [`Renaming`]s of axes. They may forget axes; the
//! kind map follows from the axis map. [`IntoStockFlow`] sends this
//! institution into [`stock_flow::StockFlowInstitution`], whose graded
//! translation both institutions share.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error as StdError;
use std::fmt;
use std::marker::PhantomData;
use std::sync::Arc;

use conservation_core::{AxisId, BalanceLawError, GradedLaw, Kind};
use conservation_dynamics::{FlowTopology, StockDefinition, StockId};
use conservation_stock_flow::{
    GradedStateLaw, SentenceId, StockAxisDefinition, StockFlowCarrier, StockFlowError, Symbol,
};
use conservation_trace::{LawVerdict, TraceError, TraceState, TraceStateError, check_law};
use institution::{Comorphism, Institution, Renaming, RenamingError, Vocabulary};

use crate::stock_flow::{
    AxisVocabulary, StockFlowInstitution, StockFlowModel, StockFlowSentence, StockFlowSignature,
    translate_graded,
};

pub mod stock_flow;

/// A vocabulary whose every symbol carries a quantity kind.
///
/// A renaming's kind map is not supplied beside its symbol map: it is derived
/// from it, sending each source symbol's kind to its image's kind.
pub(crate) trait Kinded: Vocabulary {
    type Kind: Kind;

    /// The kind of a symbol of this vocabulary.
    fn kind_of(&self, symbol: &Self::Symbol) -> Option<Self::Kind>;
}

/// A symbol whose image gives its kind a second image.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KindConflict<S, K> {
    /// The source symbol whose image disagrees.
    pub symbol: S,
    /// The kind of `symbol`.
    pub kind: K,
    /// The image of `kind` given by earlier symbols.
    pub first: K,
    /// The kind of the image of `symbol`.
    pub second: K,
}

impl<S: fmt::Debug, K: Kind> fmt::Display for KindConflict<S, K> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "kind {} goes to {} but the image of {:?} is {}",
            self.kind, self.first, self.symbol, self.second
        )
    }
}

/// Checks that `renaming` induces one kind map: every source symbol of one
/// kind has an image of one kind. The map need not be injective.
pub(crate) fn check_derived_kinds<V: Kinded>(
    renaming: &Renaming<V>,
) -> Result<(), KindConflict<V::Symbol, V::Kind>> {
    let mut kinds = BTreeMap::new();
    for (from, to) in renaming.pairs() {
        let kind = symbol_kind(renaming.source(), from);
        let image = symbol_kind(renaming.target(), to);
        if let Some(first) = kinds.insert(kind, image) {
            if first != image {
                return Err(KindConflict {
                    symbol: from.clone(),
                    kind,
                    first,
                    second: image,
                });
            }
        }
    }
    Ok(())
}

/// The kind `renaming` sends `kind` to, when `kind` is a kind of its source.
pub(crate) fn kind_image<V: Kinded>(renaming: &Renaming<V>, kind: V::Kind) -> Option<V::Kind> {
    renaming
        .pairs()
        .find(|(from, _)| symbol_kind(renaming.source(), from) == kind)
        .map(|(_, to)| symbol_kind(renaming.target(), to))
}

pub(crate) fn symbol_kind<V: Kinded>(vocabulary: &V, symbol: &V::Symbol) -> V::Kind {
    vocabulary
        .kind_of(symbol)
        .expect("a validated renaming names only its vocabularies' symbols")
}

/// A nonempty assignment of every axis to its quantitative kind.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConservationSignature<K> {
    axes: BTreeMap<AxisId, K>,
    kinds: BTreeSet<K>,
}

impl<K: Kind> ConservationSignature<K> {
    /// Validates and constructs a conservation signature.
    pub fn new(axes: impl IntoIterator<Item = (AxisId, K)>) -> Result<Self, Error<K>> {
        let mut canonical = BTreeMap::new();
        for (axis, kind) in axes {
            if canonical.insert(axis.clone(), kind).is_some() {
                return Err(Error::DuplicateSignatureAxis(axis));
            }
        }
        if canonical.is_empty() {
            return Err(Error::EmptySignature);
        }
        let kinds = canonical.values().copied().collect();
        Ok(Self {
            axes: canonical,
            kinds,
        })
    }

    /// Returns the kind assigned to an axis.
    pub fn kind(&self, axis: &AxisId) -> Option<K> {
        self.axes.get(axis).copied()
    }

    /// Iterates through axes and kinds in deterministic axis order.
    pub fn axes(&self) -> impl ExactSizeIterator<Item = (&AxisId, K)> {
        self.axes.iter().map(|(axis, kind)| (axis, *kind))
    }

    /// Iterates through distinct kinds in deterministic order.
    pub fn kinds(&self) -> impl ExactSizeIterator<Item = K> {
        self.kinds.iter().copied()
    }

    /// Returns the number of axes.
    pub fn len(&self) -> usize {
        self.axes.len()
    }

    /// Returns whether this signature has no axes.
    ///
    /// Validated signatures always return `false`.
    pub fn is_empty(&self) -> bool {
        self.axes.is_empty()
    }
}

/// A renaming of axes must derive one kind map; it may forget axes.
impl<K: Kind> Vocabulary for ConservationSignature<K> {
    type Symbol = AxisId;
    type Error = Error<K>;

    fn symbols(&self) -> Vec<AxisId> {
        self.axes.keys().cloned().collect()
    }

    fn check(renaming: &Renaming<Self>) -> Result<(), Error<K>> {
        check_derived_kinds(renaming).map_err(Error::KindConflict)
    }
}

impl<K: Kind> Kinded for ConservationSignature<K> {
    type Kind = K;

    fn kind_of(&self, axis: &AxisId) -> Option<K> {
        self.kind(axis)
    }
}

impl<K: Kind> AxisVocabulary for ConservationSignature<K> {
    fn axis_image<'a>(renaming: &'a Renaming<Self>, axis: &AxisId) -> Result<&'a AxisId, Error<K>> {
        renaming
            .image(axis)
            .ok_or_else(|| Error::Renaming(RenamingError::Unnamed(axis.clone())))
    }

    fn unknown_kind(kind: K) -> Error<K> {
        Error::KindOutsideSignature(kind)
    }
}

/// A validated model containing at least two exact trace states.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraceModel<K> {
    signature: ConservationSignature<K>,
    states: Vec<TraceState>,
}

impl<K: Kind> TraceModel<K> {
    /// Constructs a model whose every state has exactly the signature's axes.
    pub fn new(
        signature: ConservationSignature<K>,
        states: Vec<TraceState>,
    ) -> Result<Self, Error<K>> {
        if states.len() < 2 {
            return Err(Error::TraceTooShort {
                states: states.len(),
            });
        }

        for (state_index, state) in states.iter().enumerate() {
            let state_axes = state.axes();
            let signature_axes = signature.axes().map(|(axis, _)| axis);
            if !state_axes.eq(signature_axes) {
                return Err(Error::ModelAxisSetMismatch { state_index });
            }
        }

        Ok(Self { signature, states })
    }

    /// Returns the model's signature.
    pub fn signature(&self) -> &ConservationSignature<K> {
        &self.signature
    }

    /// Returns the model's exact trace states.
    pub fn states(&self) -> &[TraceState] {
        &self.states
    }
}

/// Errors produced by validated bridge construction and institution operations.
#[derive(Clone, Debug, Eq, PartialEq)]
#[non_exhaustive]
pub enum Error<K> {
    /// A signature was empty.
    EmptySignature,
    /// A signature repeated an axis.
    DuplicateSignatureAxis(AxisId),
    /// An axis map is not a total injective renaming.
    Renaming(RenamingError<AxisId>),
    /// An axis map induces no single kind map.
    KindConflict(KindConflict<AxisId, K>),
    /// A sentence's kind is no kind of the renaming's source.
    KindOutsideSignature(K),
    /// A renaming forgets these target axes, so [`IntoStockFlow`] cannot map
    /// it: a stock-flow renaming may not forget a stock.
    ForgetsAxes(Vec<AxisId>),
    /// A trace model had fewer than two states.
    TraceTooShort { states: usize },
    /// A trace state's exact axis set differed from its model signature.
    ModelAxisSetMismatch { state_index: usize },
    /// A model was used with a different signature.
    ModelSignatureMismatch,
    /// A sentence referenced an axis outside its operation signature.
    SentenceAxisOutsideSignature(AxisId),
    /// A sentence's kind differed from the signature kind at an axis.
    SentenceKindMismatch {
        axis: AxisId,
        sentence_kind: K,
        signature_kind: K,
    },
    /// Exact trace checking encountered malformed structure.
    Trace(TraceError),
    /// An internally reduced trace state could not be constructed.
    TraceState(TraceStateError),
    /// A translated balance law could not be constructed.
    BalanceLaw(BalanceLawError),
    /// The stock-flow side of [`IntoStockFlow`] failed.
    StockFlow(stock_flow::Error<K>),
}

impl<K: Kind> fmt::Display for Error<K> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptySignature => formatter.write_str("signature must contain at least one axis"),
            Self::DuplicateSignatureAxis(axis) => {
                write!(formatter, "duplicate signature axis {axis}")
            }
            Self::Renaming(error) => write!(formatter, "invalid axis renaming: {error}"),
            Self::KindConflict(conflict) => write!(formatter, "{conflict}"),
            Self::KindOutsideSignature(kind) => {
                write!(formatter, "kind {kind} is outside the renaming's source")
            }
            Self::ForgetsAxes(axes) => {
                write!(
                    formatter,
                    "renaming forgets axes {axes:?}, which stock-flow reads as stocks"
                )
            }
            Self::TraceTooShort { states } => {
                write!(
                    formatter,
                    "model trace has {states} states; at least two are required"
                )
            }
            Self::ModelAxisSetMismatch { state_index } => {
                write!(
                    formatter,
                    "model state {state_index} does not match its signature"
                )
            }
            Self::ModelSignatureMismatch => formatter.write_str("model signature mismatch"),
            Self::SentenceAxisOutsideSignature(axis) => {
                write!(formatter, "sentence axis {axis} is outside its signature")
            }
            Self::SentenceKindMismatch {
                axis,
                sentence_kind,
                signature_kind,
            } => write!(
                formatter,
                "sentence kind {sentence_kind} differs from {signature_kind} at axis {axis}"
            ),
            Self::Trace(error) => write!(formatter, "malformed trace: {error}"),
            Self::TraceState(error) => write!(formatter, "invalid reduced trace state: {error}"),
            Self::BalanceLaw(error) => write!(formatter, "invalid translated law: {error}"),
            Self::StockFlow(error) => write!(formatter, "stock-flow: {error}"),
        }
    }
}

impl<K: Kind> StdError for Error<K> {}

impl<K> From<RenamingError<AxisId>> for Error<K> {
    fn from(error: RenamingError<AxisId>) -> Self {
        Self::Renaming(error)
    }
}

impl<K> From<BalanceLawError> for Error<K> {
    fn from(error: BalanceLawError) -> Self {
        Self::BalanceLaw(error)
    }
}

/// The executable institution of exact balance laws and finite traces over kinds `K`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ConservationInstitution<K>(PhantomData<fn() -> K>);

impl<K> ConservationInstitution<K> {
    /// The institution over kinds `K`.
    #[must_use]
    pub const fn new() -> Self {
        Self(PhantomData)
    }
}

impl<K> Default for ConservationInstitution<K> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Kind> ConservationInstitution<K> {
    /// Evaluates a sentence over its model's signature, keeping the verdict
    /// that [`Institution::satisfies`] reads.
    pub fn evaluate(
        sentence: &GradedLaw<K>,
        model: &TraceModel<K>,
    ) -> Result<LawVerdict<K>, Error<K>> {
        Self::validate_sentence(model.signature(), sentence)?;
        check_law(sentence, model.states()).map_err(Error::Trace)
    }

    fn validate_sentence(
        signature: &ConservationSignature<K>,
        sentence: &GradedLaw<K>,
    ) -> Result<(), Error<K>> {
        let form = sentence.form();
        for (axis, _) in form.coefficients() {
            let Some(signature_kind) = signature.kind(axis) else {
                return Err(Error::SentenceAxisOutsideSignature(axis.clone()));
            };
            if form.kind() != signature_kind {
                return Err(Error::SentenceKindMismatch {
                    axis: axis.clone(),
                    sentence_kind: form.kind(),
                    signature_kind,
                });
            }
        }
        Ok(())
    }

    fn validate_model(
        signature: &ConservationSignature<K>,
        model: &TraceModel<K>,
    ) -> Result<(), Error<K>> {
        if model.signature() != signature {
            return Err(Error::ModelSignatureMismatch);
        }
        Ok(())
    }
}

impl<K: Kind> Institution for ConservationInstitution<K> {
    type Signature = ConservationSignature<K>;
    type SignatureMorphism = Renaming<ConservationSignature<K>>;
    type Sentence = GradedLaw<K>;
    type Model = TraceModel<K>;
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

    /// Translates with the graded translation stock-flow uses.
    fn translate_sentence(
        &self,
        morphism: &Self::SignatureMorphism,
        sentence: &Self::Sentence,
    ) -> Result<Self::Sentence, Self::Error> {
        Self::validate_sentence(morphism.source(), sentence)?;
        translate_graded(morphism, sentence)
    }

    /// Keeps each state's values on the renaming's image and forgets the rest.
    fn reduct(
        &self,
        morphism: &Self::SignatureMorphism,
        model: &Self::Model,
    ) -> Result<Self::Model, Self::Error> {
        Self::validate_model(morphism.target(), model)?;
        let mut states = Vec::with_capacity(model.states().len());
        for (state_index, target_state) in model.states().iter().enumerate() {
            let mut source_values = Vec::with_capacity(morphism.pairs().len());
            for (source_axis, target_axis) in morphism.pairs() {
                let value = target_state.value(target_axis).ok_or_else(|| {
                    Error::Trace(TraceError::MissingAxis {
                        state_index,
                        axis: target_axis.clone(),
                    })
                })?;
                source_values.push((source_axis.clone(), value.clone()));
            }
            states.push(TraceState::new(source_values).map_err(Error::TraceState)?);
        }
        TraceModel::new(morphism.source().clone(), states)
    }

    fn satisfies(
        &self,
        signature: &Self::Signature,
        model: &Self::Model,
        sentence: &Self::Sentence,
    ) -> Result<bool, Self::Error> {
        Self::validate_model(signature, model)?;
        Ok(match Self::evaluate(sentence, model)? {
            LawVerdict::Satisfied(_) => true,
            LawVerdict::Violated(_) => false,
        })
    }
}

/// The comorphism from conservation into stock-flow: each axis becomes an
/// unconnected stock, each law a graded state sentence, and a transition
/// trace reduces to its sequence of stock states.
///
/// It is a comorphism on the subcategory of axis-bijective renamings.
/// Signatures, sentences and models map totally; a renaming that forgets
/// axes is refused with [`Error::ForgetsAxes`], because its image would forget
/// stocks, which the stock-flow transition equation reads.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IntoStockFlow<K> {
    conservation: ConservationInstitution<K>,
    stock_flow: StockFlowInstitution<K>,
    id: SentenceId,
}

impl<K> IntoStockFlow<K> {
    /// The comorphism that names every translated law `id`.
    #[must_use]
    pub const fn new(id: SentenceId) -> Self {
        Self {
            conservation: ConservationInstitution::new(),
            stock_flow: StockFlowInstitution::new(),
            id,
        }
    }
}

impl<K: Kind> Comorphism for IntoStockFlow<K> {
    type Source = ConservationInstitution<K>;
    type Target = StockFlowInstitution<K>;
    type Error = Error<K>;

    fn source_institution(&self) -> &Self::Source {
        &self.conservation
    }

    fn target_institution(&self) -> &Self::Target {
        &self.stock_flow
    }

    fn map_signature(
        &self,
        signature: &ConservationSignature<K>,
    ) -> Result<StockFlowSignature<K>, Error<K>> {
        let mut stocks = Vec::with_capacity(signature.len());
        for (axis, kind) in signature.axes() {
            let stock = StockId::new(axis.as_str()).map_err(|error| {
                Error::StockFlow(stock_flow::Error::StockIdentifier {
                    axis: axis.clone(),
                    error,
                })
            })?;
            stocks.push((axis.clone(), stock, kind));
        }
        let topology = FlowTopology::new(
            stocks.iter().map(|(_, stock, kind)| StockDefinition {
                id: stock.clone(),
                kind: *kind,
            }),
            [],
            [],
        )
        .map_err(|error| Error::StockFlow(StockFlowError::from(error).into()))?;
        let carrier = StockFlowCarrier::new(
            Arc::new(topology),
            stocks
                .into_iter()
                .map(|(axis, stock, _)| StockAxisDefinition { stock, axis }),
            [],
            [],
        )
        .map_err(|error| Error::StockFlow(error.into()))?;
        Ok(StockFlowSignature::new(Arc::new(carrier)))
    }

    fn map_signature_morphism(
        &self,
        morphism: &Renaming<ConservationSignature<K>>,
    ) -> Result<Renaming<StockFlowSignature<K>>, Error<K>> {
        let forgotten = morphism
            .target()
            .symbols()
            .into_iter()
            .filter(|axis| morphism.preimage(axis).is_none())
            .collect::<Vec<_>>();
        if !forgotten.is_empty() {
            return Err(Error::ForgetsAxes(forgotten));
        }
        Renaming::new(
            self.map_signature(morphism.source())?,
            self.map_signature(morphism.target())?,
            morphism
                .pairs()
                .map(|(from, to)| (from.symbol_id(), to.symbol_id())),
        )
        .map_err(Error::StockFlow)
    }

    fn translate_sentence(
        &self,
        signature: &ConservationSignature<K>,
        sentence: &GradedLaw<K>,
    ) -> Result<StockFlowSentence<K>, Error<K>> {
        ConservationInstitution::validate_sentence(signature, sentence)?;
        Ok(StockFlowSentence::Graded(GradedStateLaw::new(
            self.id.clone(),
            sentence.clone(),
        )))
    }

    fn reduct(
        &self,
        signature: &ConservationSignature<K>,
        model: &StockFlowModel<K>,
    ) -> Result<TraceModel<K>, Error<K>> {
        if model.signature() != &self.map_signature(signature)? {
            return Err(Error::StockFlow(stock_flow::Error::ModelSignatureMismatch));
        }
        let states = model
            .trace()
            .graded_states()
            .map_err(|error| Error::StockFlow(error.into()))?;
        TraceModel::new(signature.clone(), states)
    }
}
