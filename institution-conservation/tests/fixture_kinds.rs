mod support;

use conservation_core::{Affine, Kind, KindRegistry};
use support::FixtureKind;
use support::kinds::FixtureKinds;

#[test]
fn fixture_kinds_resolve_every_declared_name_and_nothing_else() {
    for kind in FixtureKind::ALL {
        assert_eq!(FixtureKinds.resolve(kind.name()), Some(kind));
        assert_eq!(kind.to_string(), kind.name());
    }
    assert_eq!(FixtureKinds.resolve("Money"), None);
    assert_eq!(FixtureKinds.resolve(""), None);
    assert_eq!(FixtureKinds.resolve("material"), None);
}

#[test]
fn fixture_kind_declaration_order_is_name_order() {
    for pair in FixtureKind::ALL.windows(2) {
        let (a, b) = (pair[0], pair[1]);
        assert!(a < b, "{a:?} is not before {b:?}");
        assert!(a.name() < b.name(), "{a} is not before {b} by name");
    }
}

#[test]
fn fixture_kinds_are_linear_and_unfloored() {
    for kind in FixtureKind::ALL {
        assert_eq!(kind.affine(), Affine::Linear, "{kind} is not linear");
        assert!(kind.floor().is_none(), "{kind} has a floor");
    }
}
