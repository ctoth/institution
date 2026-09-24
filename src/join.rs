//! A generic institution joining two institutions with bridge sentences.

use core::fmt;
use std::error::Error as StdError;

use crate::Institution;
use crate::comorphism::Comorphism;

/// One value of each part: the joined signature, model, or morphism parts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Pair<L, R> {
    /// The left part's value.
    pub left: L,
    /// The right part's value.
    pub right: R,
}

/// Sentences of a joined institution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum JoinedSentence<L, R, B> {
    /// A sentence of the left part.
    Left(L),
    /// A sentence of the right part.
    Right(R),
    /// A bridge sentence relating both parts.
    Bridge(B),
}

/// A joined signature morphism: its endpoints and one morphism of each part.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JoinedMorphism<S, M> {
    source: S,
    target: S,
    parts: M,
}

impl<S, M> JoinedMorphism<S, M> {
    /// One morphism of each part.
    pub fn parts(&self) -> &M {
        &self.parts
    }
}

/// A failure of a joined operation, kept with the part that produced it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum JoinError<L, R, B> {
    /// The left institution failed.
    Left(L),
    /// The right institution failed.
    Right(R),
    /// The bridge failed.
    Bridge(B),
}

impl<L, R, B> fmt::Display for JoinError<L, R, B>
where
    L: fmt::Display,
    R: fmt::Display,
    B: fmt::Display,
{
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Left(error) => write!(formatter, "left institution: {error}"),
            Self::Right(error) => write!(formatter, "right institution: {error}"),
            Self::Bridge(error) => write!(formatter, "bridge: {error}"),
        }
    }
}

impl<L, R, B> StdError for JoinError<L, R, B>
where
    L: StdError + 'static,
    R: StdError + 'static,
    B: StdError + 'static,
{
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Left(error) => Some(error),
            Self::Right(error) => Some(error),
            Self::Bridge(error) => Some(error),
        }
    }
}

/// The signature of a join: one signature of each part.
pub type JoinedSignature<B> = Pair<
    <<B as Bridge>::Left as Institution>::Signature,
    <<B as Bridge>::Right as Institution>::Signature,
>;

/// The signature morphism of a join: one morphism of each part.
pub type JoinedSignatureMorphism<B> = JoinedMorphism<
    JoinedSignature<B>,
    Pair<
        <<B as Bridge>::Left as Institution>::SignatureMorphism,
        <<B as Bridge>::Right as Institution>::SignatureMorphism,
    >,
>;

/// The model of a join: one model of each part.
pub type JoinedModel<B> =
    Pair<<<B as Bridge>::Left as Institution>::Model, <<B as Bridge>::Right as Institution>::Model>;

/// Sentences relating the two components of a joined model.
///
/// The consumer declares the sentence type, its translation along a joined
/// morphism, and its evaluation over a pair model. Translation and
/// evaluation must satisfy the joined satisfaction condition;
/// `laws::check_satisfaction_square` on the [`Join`] observes it.
pub trait Bridge: Sized {
    /// The left part.
    type Left: Institution;
    /// The right part.
    type Right: Institution;
    /// Bridge sentences over a joined signature.
    type Sentence;
    /// Typed evidence of one evaluation.
    type Verdict;
    /// Failures of bridge operations.
    type Error;

    /// Translates a bridge sentence along a joined morphism.
    fn translate_sentence(
        &self,
        morphism: &JoinedSignatureMorphism<Self>,
        sentence: &Self::Sentence,
    ) -> Result<Self::Sentence, Self::Error>;

    /// Evaluates a bridge sentence over a joined model, keeping the evidence.
    fn evaluate(
        &self,
        signature: &JoinedSignature<Self>,
        model: &JoinedModel<Self>,
        sentence: &Self::Sentence,
    ) -> Result<Self::Verdict, Self::Error>;

    /// Whether `verdict` reports satisfaction.
    fn is_satisfied(verdict: &Self::Verdict) -> bool;
}

/// Two institutions and the bridge relating them.
pub struct Join<B: Bridge> {
    left: B::Left,
    right: B::Right,
    bridge: B,
}

impl<B: Bridge> Join<B> {
    /// Joins `left` and `right` through `bridge`.
    pub fn new(left: B::Left, right: B::Right, bridge: B) -> Self {
        Self {
            left,
            right,
            bridge,
        }
    }

    /// The left part.
    pub fn left(&self) -> &B::Left {
        &self.left
    }

    /// The right part.
    pub fn right(&self) -> &B::Right {
        &self.right
    }

    /// The bridge.
    pub fn bridge(&self) -> &B {
        &self.bridge
    }

    /// Pairs one morphism of each part. Endpoints are cloned from the parts.
    pub fn morphism(
        &self,
        left: <B::Left as Institution>::SignatureMorphism,
        right: <B::Right as Institution>::SignatureMorphism,
    ) -> JoinedSignatureMorphism<B>
    where
        <B::Left as Institution>::Signature: Clone,
        <B::Right as Institution>::Signature: Clone,
    {
        let source = Pair {
            left: self.left.source(&left).clone(),
            right: self.right.source(&right).clone(),
        };
        let target = Pair {
            left: self.left.target(&left).clone(),
            right: self.right.target(&right).clone(),
        };
        JoinedMorphism {
            source,
            target,
            parts: Pair { left, right },
        }
    }

    /// Embeds the left part with the right component fixed at `right`.
    pub fn embed_left(&self, right: <B::Right as Institution>::Signature) -> LeftEmbedding<'_, B> {
        LeftEmbedding { join: self, right }
    }

    /// Embeds the right part with the left component fixed at `left`.
    pub fn embed_right(&self, left: <B::Left as Institution>::Signature) -> RightEmbedding<'_, B> {
        RightEmbedding { join: self, left }
    }
}

impl<B> Institution for Join<B>
where
    B: Bridge,
    <B::Left as Institution>::Signature: Clone,
    <B::Right as Institution>::Signature: Clone,
{
    type Signature = JoinedSignature<B>;
    type SignatureMorphism = JoinedSignatureMorphism<B>;
    type Sentence = JoinedSentence<
        <B::Left as Institution>::Sentence,
        <B::Right as Institution>::Sentence,
        B::Sentence,
    >;
    type Model = JoinedModel<B>;
    type Error =
        JoinError<<B::Left as Institution>::Error, <B::Right as Institution>::Error, B::Error>;

    fn source<'a>(&self, morphism: &'a Self::SignatureMorphism) -> &'a Self::Signature {
        &morphism.source
    }

    fn target<'a>(&self, morphism: &'a Self::SignatureMorphism) -> &'a Self::Signature {
        &morphism.target
    }

    fn identity(
        &self,
        signature: &Self::Signature,
    ) -> Result<Self::SignatureMorphism, Self::Error> {
        let parts = Pair {
            left: self
                .left
                .identity(&signature.left)
                .map_err(JoinError::Left)?,
            right: self
                .right
                .identity(&signature.right)
                .map_err(JoinError::Right)?,
        };
        Ok(JoinedMorphism {
            source: signature.clone(),
            target: signature.clone(),
            parts,
        })
    }

    fn compose(
        &self,
        first: &Self::SignatureMorphism,
        second: &Self::SignatureMorphism,
    ) -> Result<Self::SignatureMorphism, Self::Error> {
        let parts = Pair {
            left: self
                .left
                .compose(&first.parts.left, &second.parts.left)
                .map_err(JoinError::Left)?,
            right: self
                .right
                .compose(&first.parts.right, &second.parts.right)
                .map_err(JoinError::Right)?,
        };
        Ok(JoinedMorphism {
            source: first.source.clone(),
            target: second.target.clone(),
            parts,
        })
    }

    fn translate_sentence(
        &self,
        morphism: &Self::SignatureMorphism,
        sentence: &Self::Sentence,
    ) -> Result<Self::Sentence, Self::Error> {
        match sentence {
            JoinedSentence::Left(sentence) => self
                .left
                .translate_sentence(&morphism.parts.left, sentence)
                .map(JoinedSentence::Left)
                .map_err(JoinError::Left),
            JoinedSentence::Right(sentence) => self
                .right
                .translate_sentence(&morphism.parts.right, sentence)
                .map(JoinedSentence::Right)
                .map_err(JoinError::Right),
            JoinedSentence::Bridge(sentence) => self
                .bridge
                .translate_sentence(morphism, sentence)
                .map(JoinedSentence::Bridge)
                .map_err(JoinError::Bridge),
        }
    }

    fn reduct(
        &self,
        morphism: &Self::SignatureMorphism,
        model: &Self::Model,
    ) -> Result<Self::Model, Self::Error> {
        Ok(Pair {
            left: self
                .left
                .reduct(&morphism.parts.left, &model.left)
                .map_err(JoinError::Left)?,
            right: self
                .right
                .reduct(&morphism.parts.right, &model.right)
                .map_err(JoinError::Right)?,
        })
    }

    fn satisfies(
        &self,
        signature: &Self::Signature,
        model: &Self::Model,
        sentence: &Self::Sentence,
    ) -> Result<bool, Self::Error> {
        match sentence {
            JoinedSentence::Left(sentence) => self
                .left
                .satisfies(&signature.left, &model.left, sentence)
                .map_err(JoinError::Left),
            JoinedSentence::Right(sentence) => self
                .right
                .satisfies(&signature.right, &model.right, sentence)
                .map_err(JoinError::Right),
            JoinedSentence::Bridge(sentence) => self
                .bridge
                .evaluate(signature, model, sentence)
                .map(|verdict| B::is_satisfied(&verdict))
                .map_err(JoinError::Bridge),
        }
    }
}

/// The left part's comorphism into the join, for a fixed right signature.
pub struct LeftEmbedding<'a, B: Bridge> {
    join: &'a Join<B>,
    right: <B::Right as Institution>::Signature,
}

impl<'a, B> Comorphism for LeftEmbedding<'a, B>
where
    B: Bridge,
    <B::Left as Institution>::Signature: Clone,
    <B::Right as Institution>::Signature: Clone,
    <B::Left as Institution>::Sentence: Clone,
    <B::Left as Institution>::Model: Clone,
    <B::Left as Institution>::SignatureMorphism: Clone,
{
    type Source = B::Left;
    type Target = Join<B>;
    /// Only mapping a morphism can fail: it needs the right part's identity.
    type Error = <B::Right as Institution>::Error;

    fn source_institution(&self) -> &Self::Source {
        self.join.left()
    }

    fn target_institution(&self) -> &Self::Target {
        self.join
    }

    fn map_signature(
        &self,
        signature: &<Self::Source as Institution>::Signature,
    ) -> Result<<Self::Target as Institution>::Signature, Self::Error> {
        Ok(Pair {
            left: signature.clone(),
            right: self.right.clone(),
        })
    }

    fn map_signature_morphism(
        &self,
        morphism: &<Self::Source as Institution>::SignatureMorphism,
    ) -> Result<<Self::Target as Institution>::SignatureMorphism, Self::Error> {
        let identity = self.join.right().identity(&self.right)?;
        Ok(self.join.morphism(morphism.clone(), identity))
    }

    fn translate_sentence(
        &self,
        _signature: &<Self::Source as Institution>::Signature,
        sentence: &<Self::Source as Institution>::Sentence,
    ) -> Result<<Self::Target as Institution>::Sentence, Self::Error> {
        Ok(JoinedSentence::Left(sentence.clone()))
    }

    fn reduct(
        &self,
        _signature: &<Self::Source as Institution>::Signature,
        model: &<Self::Target as Institution>::Model,
    ) -> Result<<Self::Source as Institution>::Model, Self::Error> {
        Ok(model.left.clone())
    }
}

/// The right part's comorphism into the join, for a fixed left signature.
pub struct RightEmbedding<'a, B: Bridge> {
    join: &'a Join<B>,
    left: <B::Left as Institution>::Signature,
}

impl<'a, B> Comorphism for RightEmbedding<'a, B>
where
    B: Bridge,
    <B::Left as Institution>::Signature: Clone,
    <B::Right as Institution>::Signature: Clone,
    <B::Right as Institution>::Sentence: Clone,
    <B::Right as Institution>::Model: Clone,
    <B::Right as Institution>::SignatureMorphism: Clone,
{
    type Source = B::Right;
    type Target = Join<B>;
    /// Only mapping a morphism can fail: it needs the left part's identity.
    type Error = <B::Left as Institution>::Error;

    fn source_institution(&self) -> &Self::Source {
        self.join.right()
    }

    fn target_institution(&self) -> &Self::Target {
        self.join
    }

    fn map_signature(
        &self,
        signature: &<Self::Source as Institution>::Signature,
    ) -> Result<<Self::Target as Institution>::Signature, Self::Error> {
        Ok(Pair {
            left: self.left.clone(),
            right: signature.clone(),
        })
    }

    fn map_signature_morphism(
        &self,
        morphism: &<Self::Source as Institution>::SignatureMorphism,
    ) -> Result<<Self::Target as Institution>::SignatureMorphism, Self::Error> {
        let identity = self.join.left().identity(&self.left)?;
        Ok(self.join.morphism(identity, morphism.clone()))
    }

    fn translate_sentence(
        &self,
        _signature: &<Self::Source as Institution>::Signature,
        sentence: &<Self::Source as Institution>::Sentence,
    ) -> Result<<Self::Target as Institution>::Sentence, Self::Error> {
        Ok(JoinedSentence::Right(sentence.clone()))
    }

    fn reduct(
        &self,
        _signature: &<Self::Source as Institution>::Signature,
        model: &<Self::Target as Institution>::Model,
    ) -> Result<<Self::Source as Institution>::Model, Self::Error> {
        Ok(model.right.clone())
    }
}
