//! The kinds named by institution-conservation's tests. They are fixtures, not physics:
//! every kind is linear and has no floor.

use std::fmt;

use conservation_core::{Affine, Kind};
use num_rational::BigRational;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FixtureKind {
    Biomass,
    BiomassEnergy,
    Currency,
    Energy,
    Mass,
    Measure,
    Money,
    NeutralEnergy,
    NeutralQuantity,
    Outside,
    Q1,
    Q2,
    Quantity,
    R1,
    R2,
}

impl fmt::Display for FixtureKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, formatter)
    }
}

impl Kind for FixtureKind {
    fn affine(self) -> Affine<Self> {
        Affine::Linear
    }

    fn floor(self) -> Option<BigRational> {
        None
    }
}
