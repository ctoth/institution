use conservation_bridgman::BridgmanKinds;
use conservation_core::{AxisId, Kind, KindRegistry};
use institution_conservation::ConservationSignature;

#[test]
fn physical_stock_kinds_are_accepted_without_a_second_registry() {
    let kinds = BridgmanKinds::thermal().unwrap();
    let enthalpy = kinds.resolve("enthalpy").unwrap();
    let signature = ConservationSignature::new([(AxisId::new("body").unwrap(), enthalpy)]).unwrap();
    assert_eq!(
        signature.kind(&AxisId::new("body").unwrap()),
        Some(enthalpy)
    );
    assert_eq!(enthalpy.difference(), kinds.resolve("energy").unwrap());
}
