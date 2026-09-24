#![forbid(unsafe_code)]

//! The institution of graded conservation sentences and finite traces.
//!
//! Sentences are [`GradedLaw`]s: one exact linear form read as an invariant
//! balance, a nonnegativity constraint, or a nondecreasing (dissipation)
//! constraint. Translation renames the form and preserves the grade, so one
//! satisfaction condition covers every grade.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error as StdError;
use std::fmt;
use std::marker::PhantomData;

use conservation_core::{AxisId, BalanceLaw, BalanceLawError, GradedLaw, Kind};
use conservation_trace::{LawVerdict, TraceError, TraceState, TraceStateError, check_law};
use institution::Institution;

pub mod stock_flow;

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

/// A bijective, kind-preserving renaming with explicit source and target.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AxisRenaming<K> {
    source: ConservationSignature<K>,
    target: ConservationSignature<K>,
    forward: BTreeMap<AxisId, AxisId>,
    inverse: BTreeMap<AxisId, AxisId>,
    kind_forward: BTreeMap<K, K>,
}

impl<K: Kind> AxisRenaming<K> {
    /// Validates and constructs an axis renaming.
    pub fn new(
        source: ConservationSignature<K>,
        target: ConservationSignature<K>,
        mappings: impl IntoIterator<Item = (AxisId, AxisId)>,
        kind_mappings: impl IntoIterator<Item = (K, K)>,
    ) -> Result<Self, Error<K>> {
        let mut kind_forward = BTreeMap::<K, K>::new();
        let mut kind_inverse = BTreeMap::<K, K>::new();
        for (source_kind, target_kind) in kind_mappings {
            if !source.kinds.contains(&source_kind) {
                return Err(Error::KindMappingSourceOutsideSignature(source_kind));
            }
            if !target.kinds.contains(&target_kind) {
                return Err(Error::KindMappingTargetOutsideSignature(target_kind));
            }
            if let Some(&existing_target) = kind_forward.get(&source_kind) {
                if existing_target == target_kind {
                    return Err(Error::DuplicateSourceKind(source_kind));
                }
                return Err(Error::ConflictingKindMapping {
                    source_kind,
                    first_target: existing_target,
                    second_target: target_kind,
                });
            }
            if kind_inverse.insert(target_kind, source_kind).is_some() {
                return Err(Error::DuplicateTargetKind(target_kind));
            }
            kind_forward.insert(source_kind, target_kind);
        }
        if kind_forward.len() != source.kinds.len() {
            return Err(Error::IncompleteKindRenaming {
                mapped: kind_forward.len(),
                source_kinds: source.kinds.len(),
            });
        }
        if kind_inverse.len() != target.kinds.len() {
            return Err(Error::NonBijectiveKindRenaming {
                mapped_targets: kind_inverse.len(),
                target_kinds: target.kinds.len(),
            });
        }

        let mut forward = BTreeMap::new();
        let mut inverse = BTreeMap::new();

        for (source_axis, target_axis) in mappings {
            let Some(source_kind) = source.kind(&source_axis) else {
                return Err(Error::RenamingSourceAxisOutsideSignature(source_axis));
            };
            let Some(target_kind) = target.kind(&target_axis) else {
                return Err(Error::RenamingTargetAxisOutsideSignature(target_axis));
            };
            let mapped_kind = kind_forward
                .get(&source_kind)
                .copied()
                .ok_or(Error::KindMappingSourceOutsideSignature(source_kind))?;
            if mapped_kind != target_kind {
                return Err(Error::AxisKindMappingMismatch {
                    source_axis,
                    target_axis,
                    mapped_kind,
                    target_kind,
                });
            }
            if forward
                .insert(source_axis.clone(), target_axis.clone())
                .is_some()
            {
                return Err(Error::DuplicateSourceAxis(source_axis));
            }
            if inverse.insert(target_axis.clone(), source_axis).is_some() {
                return Err(Error::DuplicateTargetAxis(target_axis));
            }
        }

        if forward.len() != source.len() {
            return Err(Error::IncompleteRenaming {
                mapped: forward.len(),
                source_axes: source.len(),
            });
        }
        if inverse.len() != target.len() {
            return Err(Error::NonBijectiveRenaming {
                mapped_targets: inverse.len(),
                target_axes: target.len(),
            });
        }

        Ok(Self {
            source,
            target,
            forward,
            inverse,
            kind_forward,
        })
    }

    /// Returns the explicit source signature.
    pub fn source(&self) -> &ConservationSignature<K> {
        &self.source
    }

    /// Returns the explicit target signature.
    pub fn target(&self) -> &ConservationSignature<K> {
        &self.target
    }

    fn identity(signature: &ConservationSignature<K>) -> Result<Self, Error<K>> {
        Self::new(
            signature.clone(),
            signature.clone(),
            signature
                .axes()
                .map(|(axis, _)| (axis.clone(), axis.clone())),
            signature.kinds().map(|kind| (kind, kind)),
        )
    }

    fn compose(first: &Self, second: &Self) -> Result<Self, Error<K>> {
        if first.target != second.source {
            return Err(Error::NonComposableRenamings);
        }
        let mappings = first
            .forward
            .iter()
            .map(|(source, middle)| {
                let target = second
                    .forward
                    .get(middle)
                    .expect("validated second renaming covers its source");
                (source.clone(), target.clone())
            })
            .collect::<Vec<_>>();
        let kind_mappings = first
            .kind_forward
            .iter()
            .map(|(source, middle)| {
                let target = second
                    .kind_forward
                    .get(middle)
                    .expect("validated second kind renaming covers its source");
                (*source, *target)
            })
            .collect::<Vec<_>>();
        Self::new(
            first.source.clone(),
            second.target.clone(),
            mappings,
            kind_mappings,
        )
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
    /// A mapping source did not belong to the source signature.
    RenamingSourceAxisOutsideSignature(AxisId),
    /// A mapping target did not belong to the target signature.
    RenamingTargetAxisOutsideSignature(AxisId),
    /// A source axis occurred more than once in a mapping input.
    DuplicateSourceAxis(AxisId),
    /// A target axis had more than one preimage.
    DuplicateTargetAxis(AxisId),
    /// A kind-map source was outside the source signature.
    KindMappingSourceOutsideSignature(K),
    /// A kind-map target was outside the target signature.
    KindMappingTargetOutsideSignature(K),
    /// An identical source-kind mapping was supplied more than once.
    DuplicateSourceKind(K),
    /// A target kind had more than one source-kind preimage.
    DuplicateTargetKind(K),
    /// One source kind was assigned two different target kinds.
    ConflictingKindMapping {
        source_kind: K,
        first_target: K,
        second_target: K,
    },
    /// Not every distinct source kind was mapped.
    IncompleteKindRenaming { mapped: usize, source_kinds: usize },
    /// The kind-map image did not cover the target kinds exactly.
    NonBijectiveKindRenaming {
        mapped_targets: usize,
        target_kinds: usize,
    },
    /// An axis mapping disagreed with the validated kind-symbol mapping.
    AxisKindMappingMismatch {
        source_axis: AxisId,
        target_axis: AxisId,
        mapped_kind: K,
        target_kind: K,
    },
    /// Not every source axis was mapped.
    IncompleteRenaming { mapped: usize, source_axes: usize },
    /// The mapped targets did not cover the target signature exactly.
    NonBijectiveRenaming {
        mapped_targets: usize,
        target_axes: usize,
    },
    /// Two signature renamings did not share the required middle signature.
    NonComposableRenamings,
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
}

impl<K: Kind> fmt::Display for Error<K> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptySignature => formatter.write_str("signature must contain at least one axis"),
            Self::DuplicateSignatureAxis(axis) => {
                write!(formatter, "duplicate signature axis {axis}")
            }
            Self::RenamingSourceAxisOutsideSignature(axis) => {
                write!(
                    formatter,
                    "renaming source axis {axis} is outside its signature"
                )
            }
            Self::RenamingTargetAxisOutsideSignature(axis) => {
                write!(
                    formatter,
                    "renaming target axis {axis} is outside its signature"
                )
            }
            Self::DuplicateSourceAxis(axis) => write!(formatter, "duplicate source axis {axis}"),
            Self::DuplicateTargetAxis(axis) => write!(formatter, "duplicate target axis {axis}"),
            Self::KindMappingSourceOutsideSignature(kind) => {
                write!(formatter, "kind-map source {kind} is outside its signature")
            }
            Self::KindMappingTargetOutsideSignature(kind) => {
                write!(formatter, "kind-map target {kind} is outside its signature")
            }
            Self::DuplicateSourceKind(kind) => write!(formatter, "duplicate source kind {kind}"),
            Self::DuplicateTargetKind(kind) => write!(formatter, "duplicate target kind {kind}"),
            Self::ConflictingKindMapping {
                source_kind,
                first_target,
                second_target,
            } => write!(
                formatter,
                "source kind {source_kind} maps to both {first_target} and {second_target}"
            ),
            Self::IncompleteKindRenaming {
                mapped,
                source_kinds,
            } => write!(
                formatter,
                "kind renaming maps {mapped} of {source_kinds} source kinds"
            ),
            Self::NonBijectiveKindRenaming {
                mapped_targets,
                target_kinds,
            } => write!(
                formatter,
                "kind renaming covers {mapped_targets} of {target_kinds} target kinds"
            ),
            Self::AxisKindMappingMismatch {
                source_axis,
                target_axis,
                mapped_kind,
                target_kind,
            } => write!(
                formatter,
                "axis renaming {source_axis} to {target_axis}:{target_kind} conflicts with mapped kind {mapped_kind}"
            ),
            Self::IncompleteRenaming {
                mapped,
                source_axes,
            } => write!(
                formatter,
                "renaming maps {mapped} of {source_axes} source axes"
            ),
            Self::NonBijectiveRenaming {
                mapped_targets,
                target_axes,
            } => write!(
                formatter,
                "renaming covers {mapped_targets} of {target_axes} target axes"
            ),
            Self::NonComposableRenamings => {
                formatter.write_str("signature renamings are not composable")
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
        }
    }
}

impl<K: Kind> StdError for Error<K> {}

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
    type SignatureMorphism = AxisRenaming<K>;
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
        AxisRenaming::identity(signature)
    }

    fn compose(
        &self,
        first: &Self::SignatureMorphism,
        second: &Self::SignatureMorphism,
    ) -> Result<Self::SignatureMorphism, Self::Error> {
        AxisRenaming::compose(first, second)
    }

    fn translate_sentence(
        &self,
        morphism: &Self::SignatureMorphism,
        sentence: &Self::Sentence,
    ) -> Result<Self::Sentence, Self::Error> {
        Self::validate_sentence(morphism.source(), sentence)?;
        let form = sentence.form();
        let target_kind = morphism
            .kind_forward
            .get(&form.kind())
            .copied()
            .ok_or(Error::KindMappingSourceOutsideSignature(form.kind()))?;
        let mut coefficients = Vec::new();
        for (source_axis, coefficient) in form.coefficients() {
            let target_axis =
                morphism.forward.get(source_axis).cloned().ok_or_else(|| {
                    Error::RenamingSourceAxisOutsideSignature(source_axis.clone())
                })?;
            coefficients.push((target_axis, coefficient.clone()));
        }
        let translated = BalanceLaw::new(target_kind, coefficients, *form.provenance())
            .map_err(Error::BalanceLaw)?;
        Ok(GradedLaw::new(translated, sentence.grade()))
    }

    fn reduct(
        &self,
        morphism: &Self::SignatureMorphism,
        model: &Self::Model,
    ) -> Result<Self::Model, Self::Error> {
        Self::validate_model(morphism.target(), model)?;
        let mut states = Vec::with_capacity(model.states().len());
        for (state_index, target_state) in model.states().iter().enumerate() {
            let mut source_values = Vec::with_capacity(morphism.inverse.len());
            for target_axis in target_state.axes() {
                let source_axis = morphism.inverse.get(target_axis).cloned().ok_or_else(|| {
                    Error::RenamingTargetAxisOutsideSignature(target_axis.clone())
                })?;
                let value = target_state.value(target_axis).ok_or_else(|| {
                    Error::Trace(TraceError::MissingAxis {
                        state_index,
                        axis: target_axis.clone(),
                    })
                })?;
                source_values.push((source_axis, value.clone()));
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
        Self::validate_sentence(signature, sentence)?;
        match check_law(sentence, model.states()).map_err(Error::Trace)? {
            LawVerdict::Satisfied(_) => Ok(true),
            LawVerdict::Violated(_) => Ok(false),
        }
    }
}
