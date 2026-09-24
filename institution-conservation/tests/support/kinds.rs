//! The kinds named by institution-conservation's tests. They are fixtures, not physics:
//! every kind is linear and has no floor, as the former string kinds had none.

use std::fmt;

use conservation_core::{Affine, Kind, KindRegistry};
use num_rational::BigRational;

/// The variants are declared in name order, so `Ord` equals the former string order.
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

impl FixtureKind {
    /// Every variant in declaration order.
    pub const ALL: [FixtureKind; 15] = [
        FixtureKind::Biomass,
        FixtureKind::BiomassEnergy,
        FixtureKind::Currency,
        FixtureKind::Energy,
        FixtureKind::Mass,
        FixtureKind::Measure,
        FixtureKind::Money,
        FixtureKind::NeutralEnergy,
        FixtureKind::NeutralQuantity,
        FixtureKind::Outside,
        FixtureKind::Q1,
        FixtureKind::Q2,
        FixtureKind::Quantity,
        FixtureKind::R1,
        FixtureKind::R2,
    ];

    /// "biomass", "biomass_energy", "currency", "energy", "mass", "measure", "money",
    /// "neutral_energy", "neutral_quantity", "outside", "q1", "q2", "quantity", "r1", "r2".
    pub const fn name(self) -> &'static str {
        match self {
            FixtureKind::Biomass => "biomass",
            FixtureKind::BiomassEnergy => "biomass_energy",
            FixtureKind::Currency => "currency",
            FixtureKind::Energy => "energy",
            FixtureKind::Mass => "mass",
            FixtureKind::Measure => "measure",
            FixtureKind::Money => "money",
            FixtureKind::NeutralEnergy => "neutral_energy",
            FixtureKind::NeutralQuantity => "neutral_quantity",
            FixtureKind::Outside => "outside",
            FixtureKind::Q1 => "q1",
            FixtureKind::Q2 => "q2",
            FixtureKind::Quantity => "quantity",
            FixtureKind::R1 => "r1",
            FixtureKind::R2 => "r2",
        }
    }
}

impl fmt::Display for FixtureKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.name())
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

/// Resolves the tests' kind names.
#[derive(Clone, Copy, Debug)]
pub struct FixtureKinds;

impl KindRegistry for FixtureKinds {
    type Kind = FixtureKind;

    fn resolve(&self, name: &str) -> Option<FixtureKind> {
        FixtureKind::ALL
            .into_iter()
            .find(|kind| kind.name() == name)
    }
}

/// The declared kind called `name`. Panics, naming it, when `name` is undeclared.
pub fn kind(name: &str) -> FixtureKind {
    FixtureKinds
        .resolve(name)
        .unwrap_or_else(|| panic!("undeclared fixture kind {name:?}"))
}
