//! Injective renamings: the signature morphisms that forget.
//!
//! A [`Renaming`] sends every symbol of its source vocabulary to a distinct
//! symbol of its target. Sentences translate forward along it; models reduce
//! backward and forget every target symbol outside the image. A bijection is
//! the special case whose image is the whole target.
//!
//! A renaming maps a symbol to a symbol. Linear and affine charts, which would
//! send a symbol to a combination of target symbols, are not implemented; a
//! renaming exposes its map only through [`Renaming::image`],
//! [`Renaming::preimage`] and [`Renaming::pairs`], so a chart can extend what
//! it maps without changing how institutions read it.

use core::fmt;
use std::error::Error as StdError;

/// A signature whose symbols a [`Renaming`] maps.
///
/// Symbol classes, where a vocabulary has several, are the variants of its
/// [`Vocabulary::Symbol`].
pub trait Vocabulary: Clone + PartialEq {
    /// One symbol of the vocabulary.
    type Symbol: Clone + Eq + fmt::Debug;

    /// Why a symbol map is not a renaming between two such vocabularies. It
    /// keeps every symbol-level failure.
    type Error: From<RenamingError<Self::Symbol>>;

    /// Every symbol, once each, in the vocabulary's canonical order.
    fn symbols(&self) -> Vec<Self::Symbol>;

    /// Checks what `renaming` must preserve beyond being a total injective map
    /// of source symbols into target symbols, such as declarations, classes
    /// and incidence.
    fn check(renaming: &Renaming<Self>) -> Result<(), Self::Error>;
}

/// A total, injective symbol map from one vocabulary into another.
///
/// Its pairs are kept in the source's canonical symbol order, so two
/// renamings with the same map are equal however their pairs were supplied.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Renaming<V: Vocabulary> {
    source: V,
    target: V,
    pairs: Vec<(V::Symbol, V::Symbol)>,
}

impl<V: Vocabulary> Renaming<V> {
    /// Validates a renaming of every `source` symbol into `target`.
    pub fn new(
        source: V,
        target: V,
        pairs: impl IntoIterator<Item = (V::Symbol, V::Symbol)>,
    ) -> Result<Self, V::Error> {
        let source_symbols = source.symbols();
        let target_symbols = target.symbols();
        let mut supplied: Vec<(V::Symbol, V::Symbol)> = Vec::new();
        for (from, to) in pairs {
            if !source_symbols.contains(&from) {
                return Err(RenamingError::NotInSource(from).into());
            }
            if !target_symbols.contains(&to) {
                return Err(RenamingError::NotInTarget(to).into());
            }
            if supplied.iter().any(|(seen, _)| seen == &from) {
                return Err(RenamingError::Repeated(from).into());
            }
            if supplied.iter().any(|(_, seen)| seen == &to) {
                return Err(RenamingError::NotInjective(to).into());
            }
            supplied.push((from, to));
        }
        let mut pairs = Vec::with_capacity(source_symbols.len());
        for symbol in source_symbols {
            let Some(position) = supplied.iter().position(|(from, _)| from == &symbol) else {
                return Err(RenamingError::Unnamed(symbol).into());
            };
            pairs.push(supplied.swap_remove(position));
        }
        let renaming = Self {
            source,
            target,
            pairs,
        };
        V::check(&renaming)?;
        Ok(renaming)
    }

    /// The identity renaming of `signature`.
    pub fn identity(signature: &V) -> Result<Self, V::Error> {
        Self::new(
            signature.clone(),
            signature.clone(),
            signature
                .symbols()
                .into_iter()
                .map(|symbol| (symbol.clone(), symbol)),
        )
    }

    /// Composes `self: A -> B` with `second: B -> C`, producing `A -> C`.
    pub fn compose(&self, second: &Self) -> Result<Self, V::Error> {
        if self.target != second.source {
            return Err(RenamingError::NotComposable.into());
        }
        let mut pairs = Vec::with_capacity(self.pairs.len());
        for (from, middle) in &self.pairs {
            let to = second
                .image(middle)
                .ok_or_else(|| RenamingError::Unnamed(middle.clone()))?;
            pairs.push((from.clone(), to.clone()));
        }
        Self::new(self.source.clone(), second.target.clone(), pairs)
    }

    /// The source vocabulary.
    pub fn source(&self) -> &V {
        &self.source
    }

    /// The target vocabulary.
    pub fn target(&self) -> &V {
        &self.target
    }

    /// The image of a source symbol.
    pub fn image(&self, symbol: &V::Symbol) -> Option<&V::Symbol> {
        self.pairs
            .iter()
            .find(|(from, _)| from == symbol)
            .map(|(_, to)| to)
    }

    /// The source symbol a target symbol is the image of, or `None` when the
    /// renaming forgets it.
    pub fn preimage(&self, symbol: &V::Symbol) -> Option<&V::Symbol> {
        self.pairs
            .iter()
            .find(|(_, to)| to == symbol)
            .map(|(from, _)| from)
    }

    /// Every source symbol with its image, in source order.
    pub fn pairs(&self) -> impl ExactSizeIterator<Item = (&V::Symbol, &V::Symbol)> {
        self.pairs.iter().map(|(from, to)| (from, to))
    }
}

/// Why a symbol map is not a total injective renaming.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RenamingError<S> {
    /// A pair names a source symbol the source vocabulary lacks.
    NotInSource(S),
    /// A pair names a target symbol the target vocabulary lacks.
    NotInTarget(S),
    /// A source symbol was given more than one image.
    Repeated(S),
    /// Two source symbols share this image.
    NotInjective(S),
    /// A source symbol has no image.
    Unnamed(S),
    /// The first renaming's target is not the second's source.
    NotComposable,
}

impl<S: fmt::Debug> fmt::Display for RenamingError<S> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotInSource(symbol) => {
                write!(formatter, "{symbol:?} is not in the source vocabulary")
            }
            Self::NotInTarget(symbol) => {
                write!(formatter, "{symbol:?} is not in the target vocabulary")
            }
            Self::Repeated(symbol) => write!(formatter, "{symbol:?} is renamed more than once"),
            Self::NotInjective(symbol) => {
                write!(formatter, "{symbol:?} is the image of two source symbols")
            }
            Self::Unnamed(symbol) => write!(formatter, "{symbol:?} has no image"),
            Self::NotComposable => {
                formatter.write_str("renamings do not share a middle vocabulary")
            }
        }
    }
}

impl<S: fmt::Debug> StdError for RenamingError<S> {}
