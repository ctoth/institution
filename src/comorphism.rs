//! Comorphisms between institutions.

use core::fmt;
use std::error::Error as StdError;

use crate::Institution;

/// A Goguen comorphism from `Source` to `Target`.
///
/// `map_signature` and `map_signature_morphism` are the signature functor.
/// `translate_sentence` is covariant (source sentence to target sentence over
/// the mapped signature). `reduct` is contravariant (a target model over the
/// mapped signature to a source model). The satisfaction condition
/// `target_model |= translate(sentence)` iff `reduct(target_model) |= sentence`
/// is observed on examples by [`crate::laws::check_comorphism_satisfaction`].
pub trait Comorphism {
    /// The institution whose signatures, sentences and models are mapped.
    type Source: Institution;
    /// The institution receiving mapped signatures and translated sentences.
    type Target: Institution;
    /// Failures of the comorphism's own operations.
    type Error;

    /// Returns the source institution.
    fn source_institution(&self) -> &Self::Source;

    /// Returns the target institution.
    fn target_institution(&self) -> &Self::Target;

    /// Maps a source signature to a target signature.
    fn map_signature(
        &self,
        signature: &<Self::Source as Institution>::Signature,
    ) -> Result<<Self::Target as Institution>::Signature, Self::Error>;

    /// Maps a source signature morphism to a target signature morphism.
    fn map_signature_morphism(
        &self,
        morphism: &<Self::Source as Institution>::SignatureMorphism,
    ) -> Result<<Self::Target as Institution>::SignatureMorphism, Self::Error>;

    /// Translates a source sentence over `signature` into a target sentence
    /// over the mapped signature.
    fn translate_sentence(
        &self,
        signature: &<Self::Source as Institution>::Signature,
        sentence: &<Self::Source as Institution>::Sentence,
    ) -> Result<<Self::Target as Institution>::Sentence, Self::Error>;

    /// Reduces a target model over the mapped signature into a source model
    /// over `signature`.
    fn reduct(
        &self,
        signature: &<Self::Source as Institution>::Signature,
        model: &<Self::Target as Institution>::Model,
    ) -> Result<<Self::Source as Institution>::Model, Self::Error>;
}

/// A failure while observing a comorphism, kept with the side that produced it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ComorphismError<S, T, C> {
    /// The source institution failed.
    Source(S),
    /// The target institution failed.
    Target(T),
    /// The comorphism's own operation failed.
    Comorphism(C),
}

/// The error of observing comorphism `C`.
pub type ComorphismLawError<C> = ComorphismError<
    <<C as Comorphism>::Source as Institution>::Error,
    <<C as Comorphism>::Target as Institution>::Error,
    <C as Comorphism>::Error,
>;

impl<S, T, C> fmt::Display for ComorphismError<S, T, C>
where
    S: fmt::Display,
    T: fmt::Display,
    C: fmt::Display,
{
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Source(error) => write!(formatter, "source institution: {error}"),
            Self::Target(error) => write!(formatter, "target institution: {error}"),
            Self::Comorphism(error) => write!(formatter, "comorphism: {error}"),
        }
    }
}

impl<S, T, C> StdError for ComorphismError<S, T, C>
where
    S: StdError + 'static,
    T: StdError + 'static,
    C: StdError + 'static,
{
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Source(error) => Some(error),
            Self::Target(error) => Some(error),
            Self::Comorphism(error) => Some(error),
        }
    }
}
