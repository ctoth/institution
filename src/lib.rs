//! Executable foundations for Goguen-style institutions.
//!
//! An institution connects signatures, signature morphisms, sentences, models,
//! and satisfaction. Implementations are responsible for validating that each
//! sentence and model belongs to the signature supplied with an operation.

#![forbid(unsafe_code)]

pub mod laws;

/// Core executable operations of a Goguen-style institution.
///
/// For a signature morphism `m: source -> target`, sentence translation is
/// covariant (`source` to `target`) and model reduct is contravariant (`target`
/// to `source`). This trait does not encode a signature category or assert
/// identity, composition, functoriality, or universal satisfaction laws.
pub trait Institution {
    /// The language vocabulary over which sentences and models are formed.
    type Signature;

    /// A morphism carrying an explicit source and target signature.
    type SignatureMorphism;

    /// A sentence over a signature.
    type Sentence;

    /// A model over a signature.
    type Model;

    /// An error produced by executable institution operations.
    type Error;

    /// Returns the source signature of `morphism`.
    fn source<'a>(&self, morphism: &'a Self::SignatureMorphism) -> &'a Self::Signature;

    /// Returns the target signature of `morphism`.
    fn target<'a>(&self, morphism: &'a Self::SignatureMorphism) -> &'a Self::Signature;

    /// Translates a source sentence along `morphism` into a target sentence.
    fn translate_sentence(
        &self,
        morphism: &Self::SignatureMorphism,
        sentence: &Self::Sentence,
    ) -> Result<Self::Sentence, Self::Error>;

    /// Reduces a target model along `morphism` into a source model.
    fn reduct(
        &self,
        morphism: &Self::SignatureMorphism,
        model: &Self::Model,
    ) -> Result<Self::Model, Self::Error>;

    /// Decides whether `model` satisfies `sentence` over `signature`.
    fn satisfies(
        &self,
        signature: &Self::Signature,
        model: &Self::Model,
        sentence: &Self::Sentence,
    ) -> Result<bool, Self::Error>;
}
