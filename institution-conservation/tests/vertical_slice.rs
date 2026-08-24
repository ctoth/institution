use conservation_core::{AxisId, BalanceLaw, KindId, Provenance};
use conservation_linear::{NullspaceSource, TransitionMatrix, derive_left_nullspace};
use conservation_trace::TraceState;
use institution::{Institution, laws};
use institution_conservation::{
    AxisRenaming, ConservationInstitution, ConservationSignature, Error, TraceModel,
};
use num_bigint::BigInt;
use num_rational::BigRational;

fn axis(value: &str) -> AxisId {
    AxisId::new(value).unwrap()
}

fn kind(value: &str) -> KindId {
    KindId::new(value).unwrap()
}

fn q(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn signature(entries: &[(&str, &str)]) -> ConservationSignature {
    ConservationSignature::new(
        entries
            .iter()
            .map(|(axis_name, kind_name)| (axis(axis_name), kind(kind_name))),
    )
    .unwrap()
}

fn state(entries: &[(&str, i64)]) -> TraceState {
    TraceState::new(
        entries
            .iter()
            .map(|(axis_name, value)| (axis(axis_name), q(*value))),
    )
    .unwrap()
}

fn derive_law(
    left: &str,
    right: &str,
    kind_name: &str,
    rows: [Vec<BigRational>; 2],
    source: NullspaceSource,
) -> BalanceLaw {
    let matrix = TransitionMatrix::new([axis(left), axis(right)], rows.to_vec()).unwrap();
    derive_left_nullspace(&matrix, kind(kind_name), source)
        .unwrap()
        .into_iter()
        .next()
        .unwrap()
}

struct SharedCases {
    source: ConservationSignature,
    law: BalanceLaw,
    ecological_renaming: AxisRenaming,
    ecological_model: TraceModel,
    economic_renaming: AxisRenaming,
    economic_model: TraceModel,
}

fn shared_neutral_cases() -> SharedCases {
    let source = signature(&[
        ("neutral_left", "neutral_quantity"),
        ("neutral_right", "neutral_quantity"),
    ]);
    // One exact directed incidence edge gives the neutral law [1, 1].
    let law = derive_law(
        "neutral_left",
        "neutral_right",
        "neutral_quantity",
        [vec![q(-1)], vec![q(1)]],
        NullspaceSource::Incidence,
    );

    let ecological_target =
        signature(&[("consumer_pool", "biomass"), ("producer_pool", "biomass")]);
    let ecological_renaming = AxisRenaming::new(
        source.clone(),
        ecological_target.clone(),
        [
            (axis("neutral_left"), axis("consumer_pool")),
            (axis("neutral_right"), axis("producer_pool")),
        ],
        [(kind("neutral_quantity"), kind("biomass"))],
    )
    .unwrap();
    let ecological_model = TraceModel::new(
        ecological_target,
        vec![
            state(&[("consumer_pool", 2), ("producer_pool", 8)]),
            state(&[("consumer_pool", 3), ("producer_pool", 7)]),
        ],
    )
    .unwrap();

    let economic_target = signature(&[("asset_account", "money"), ("stock_account", "money")]);
    let economic_renaming = AxisRenaming::new(
        source.clone(),
        economic_target.clone(),
        [
            (axis("neutral_left"), axis("asset_account")),
            (axis("neutral_right"), axis("stock_account")),
        ],
        [(kind("neutral_quantity"), kind("money"))],
    )
    .unwrap();
    let economic_model = TraceModel::new(
        economic_target,
        vec![
            state(&[("asset_account", 6), ("stock_account", 4)]),
            state(&[("asset_account", 7), ("stock_account", 2)]),
        ],
    )
    .unwrap();

    SharedCases {
        source,
        law,
        ecological_renaming,
        ecological_model,
        economic_renaming,
        economic_model,
    }
}

#[test]
fn one_neutral_source_law_gives_true_ecological_and_false_economic_squares() {
    let cases = shared_neutral_cases();
    let institution = ConservationInstitution;

    assert_eq!(cases.ecological_renaming.source(), &cases.source);
    assert_eq!(cases.economic_renaming.source(), &cases.source);
    assert_eq!(cases.law.provenance(), &Provenance::IncidenceNullspace);
    let economic_source_law = cases.law.clone();
    assert_eq!(economic_source_law, cases.law);

    let ecological_law = institution
        .translate_sentence(&cases.ecological_renaming, &cases.law)
        .unwrap();
    let economic_law = institution
        .translate_sentence(&cases.economic_renaming, &economic_source_law)
        .unwrap();
    assert_eq!(ecological_law.kind(), &kind("biomass"));
    assert_eq!(economic_law.kind(), &kind("money"));
    assert_eq!(ecological_law.provenance(), cases.law.provenance());
    assert_eq!(economic_law.provenance(), cases.law.provenance());

    let ecological_square = laws::check_satisfaction_square(
        &institution,
        &cases.ecological_renaming,
        &cases.law,
        &cases.ecological_model,
    )
    .unwrap();
    assert!(ecological_square.holds());
    assert!(ecological_square.translated_sentence_satisfied());
    assert!(ecological_square.reduced_model_satisfies_source_sentence());

    let economic_square = laws::check_satisfaction_square(
        &institution,
        &cases.economic_renaming,
        &economic_source_law,
        &cases.economic_model,
    )
    .unwrap();
    assert!(economic_square.holds());
    assert!(!economic_square.translated_sentence_satisfied());
    assert!(!economic_square.reduced_model_satisfies_source_sentence());

    let ecological_reduct = institution
        .reduct(&cases.ecological_renaming, &cases.ecological_model)
        .unwrap();
    let economic_reduct = institution
        .reduct(&cases.economic_renaming, &cases.economic_model)
        .unwrap();
    let evidence = laws::check_non_vacuity(
        &institution,
        [
            (
                cases.ecological_renaming.target(),
                &cases.ecological_model,
                &ecological_law,
            ),
            (&cases.source, &ecological_reduct, &cases.law),
            (
                cases.economic_renaming.target(),
                &cases.economic_model,
                &economic_law,
            ),
            (&cases.source, &economic_reduct, &economic_source_law),
        ],
    )
    .unwrap();
    assert!(evidence.is_non_vacuous());
    assert_eq!(evidence.satisfying_cases(), 2);
    assert_eq!(evidence.falsifying_cases(), 2);
}

#[test]
fn asymmetric_stoichiometric_law_exposes_translation_and_reduct_direction() {
    let source = signature(&[("left", "quantity"), ("right", "quantity")]);
    // The exact stoichiometric column [2, -1] has left-nullspace basis [1, 2].
    let law = derive_law(
        "left",
        "right",
        "quantity",
        [vec![q(2)], vec![q(-1)]],
        NullspaceSource::Stoichiometric,
    );
    assert_eq!(law.coefficient(&axis("left")), &q(1));
    assert_eq!(law.coefficient(&axis("right")), &q(2));
    assert_eq!(law.provenance(), &Provenance::StoichiometricNullspace);

    let target = signature(&[("alpha", "measure"), ("zeta", "measure")]);
    let reversing = AxisRenaming::new(
        source.clone(),
        target.clone(),
        [(axis("left"), axis("zeta")), (axis("right"), axis("alpha"))],
        [(kind("quantity"), kind("measure"))],
    )
    .unwrap();
    let target_model = TraceModel::new(
        target,
        vec![
            state(&[("alpha", 20), ("zeta", 10)]),
            state(&[("alpha", 21), ("zeta", 8)]),
        ],
    )
    .unwrap();

    let translated = ConservationInstitution
        .translate_sentence(&reversing, &law)
        .unwrap();
    assert_eq!(translated.kind(), &kind("measure"));
    assert_eq!(translated.coefficient(&axis("alpha")), &q(2));
    assert_eq!(translated.coefficient(&axis("zeta")), &q(1));

    let reduced = ConservationInstitution
        .reduct(&reversing, &target_model)
        .unwrap();
    assert_eq!(reduced.signature(), &source);
    assert_eq!(reduced.states()[0].value(&axis("left")), Some(&q(10)));
    assert_eq!(reduced.states()[0].value(&axis("right")), Some(&q(20)));
}

#[test]
fn provenance_tags_do_not_change_satisfaction_semantics() {
    let source = signature(&[("left", "quantity"), ("right", "quantity")]);
    let derived = derive_law(
        "left",
        "right",
        "quantity",
        [vec![q(2)], vec![q(-1)]],
        NullspaceSource::Stoichiometric,
    );
    let declared = BalanceLaw::new(
        derived.kind().clone(),
        derived
            .coefficients()
            .map(|(axis, coefficient)| (axis.clone(), coefficient.clone())),
        Provenance::Declared,
    )
    .unwrap();
    let model = TraceModel::new(
        source.clone(),
        vec![
            state(&[("left", 10), ("right", 20)]),
            state(&[("left", 8), ("right", 21)]),
        ],
    )
    .unwrap();

    assert_eq!(derived.provenance(), &Provenance::StoichiometricNullspace);
    assert_eq!(declared.provenance(), &Provenance::Declared);
    assert_eq!(
        ConservationInstitution.satisfies(&source, &model, &derived),
        ConservationInstitution.satisfies(&source, &model, &declared)
    );
    assert_eq!(
        ConservationInstitution.satisfies(&source, &model, &derived),
        Ok(true)
    );
}

#[test]
fn signatures_axis_maps_and_models_retain_their_validation() {
    assert_eq!(ConservationSignature::new([]), Err(Error::EmptySignature));
    assert_eq!(
        ConservationSignature::new([(axis("A"), kind("quantity")), (axis("A"), kind("quantity")),]),
        Err(Error::DuplicateSignatureAxis(axis("A")))
    );

    let source = signature(&[("A", "quantity"), ("B", "quantity")]);
    let target = signature(&[("X", "measure"), ("Y", "measure")]);
    let kind_map = [(kind("quantity"), kind("measure"))];
    assert_eq!(
        AxisRenaming::new(
            source.clone(),
            target.clone(),
            [(axis("A"), axis("X"))],
            kind_map.clone(),
        ),
        Err(Error::IncompleteRenaming {
            mapped: 1,
            source_axes: 2,
        })
    );
    assert_eq!(
        AxisRenaming::new(
            source.clone(),
            target,
            [(axis("A"), axis("X")), (axis("B"), axis("X"))],
            kind_map,
        ),
        Err(Error::DuplicateTargetAxis(axis("X")))
    );

    assert_eq!(
        TraceModel::new(source.clone(), vec![state(&[("A", 1), ("B", 1)])]),
        Err(Error::TraceTooShort { states: 1 })
    );
    assert_eq!(
        TraceModel::new(
            source,
            vec![state(&[("A", 1), ("B", 1)]), state(&[("A", 2)])],
        ),
        Err(Error::ModelAxisSetMismatch { state_index: 1 })
    );
}

#[test]
fn kind_maps_reject_missing_extra_duplicate_conflicting_and_nonbijective_entries() {
    let source = signature(&[("A", "q1"), ("B", "q2")]);
    let target = signature(&[("X", "r1"), ("Y", "r2")]);
    let axes = [(axis("A"), axis("X")), (axis("B"), axis("Y"))];

    assert_eq!(
        AxisRenaming::new(
            source.clone(),
            target.clone(),
            axes.clone(),
            [(kind("q1"), kind("r1"))],
        ),
        Err(Error::IncompleteKindRenaming {
            mapped: 1,
            source_kinds: 2,
        })
    );
    assert_eq!(
        AxisRenaming::new(
            source.clone(),
            target.clone(),
            axes.clone(),
            [
                (kind("q1"), kind("r1")),
                (kind("q2"), kind("r2")),
                (kind("outside"), kind("r1")),
            ],
        ),
        Err(Error::KindMappingSourceOutsideSignature(kind("outside")))
    );
    assert_eq!(
        AxisRenaming::new(
            source.clone(),
            target.clone(),
            axes.clone(),
            [(kind("q1"), kind("r1")), (kind("q2"), kind("outside")),],
        ),
        Err(Error::KindMappingTargetOutsideSignature(kind("outside")))
    );
    assert_eq!(
        AxisRenaming::new(
            source.clone(),
            target.clone(),
            axes.clone(),
            [(kind("q1"), kind("r1")), (kind("q1"), kind("r1")),],
        ),
        Err(Error::DuplicateSourceKind(kind("q1")))
    );
    assert!(matches!(
        AxisRenaming::new(
            source.clone(),
            target.clone(),
            axes.clone(),
            [(kind("q1"), kind("r1")), (kind("q1"), kind("r2")),],
        ),
        Err(Error::ConflictingKindMapping { .. })
    ));
    assert_eq!(
        AxisRenaming::new(
            source.clone(),
            target.clone(),
            axes.clone(),
            [(kind("q1"), kind("r1")), (kind("q2"), kind("r1")),],
        ),
        Err(Error::DuplicateTargetKind(kind("r1")))
    );

    let target_with_extra_kind = signature(&[("X", "r1"), ("Y", "r1"), ("Z", "r2")]);
    let one_kind_source = signature(&[("A", "q1"), ("B", "q1")]);
    assert_eq!(
        AxisRenaming::new(
            one_kind_source,
            target_with_extra_kind,
            [(axis("A"), axis("X")), (axis("B"), axis("Y"))],
            [(kind("q1"), kind("r1"))],
        ),
        Err(Error::NonBijectiveKindRenaming {
            mapped_targets: 1,
            target_kinds: 2,
        })
    );

    let mismatched_axes = [(axis("A"), axis("Y")), (axis("B"), axis("X"))];
    assert!(matches!(
        AxisRenaming::new(
            source,
            target,
            mismatched_axes,
            [(kind("q1"), kind("r1")), (kind("q2"), kind("r2"))],
        ),
        Err(Error::AxisKindMappingMismatch { .. })
    ));
}

#[test]
fn malformed_memberships_error_instead_of_returning_false() {
    let source = signature(&[("A", "quantity"), ("B", "quantity")]);
    let model = TraceModel::new(
        source.clone(),
        vec![state(&[("A", 1), ("B", 1)]), state(&[("A", 2), ("B", 0)])],
    )
    .unwrap();
    let outside_law = BalanceLaw::new(
        kind("quantity"),
        [(axis("outside"), q(1))],
        Provenance::Declared,
    )
    .unwrap();
    assert_eq!(
        ConservationInstitution.satisfies(&source, &model, &outside_law),
        Err(Error::SentenceAxisOutsideSignature(axis("outside")))
    );

    let other = signature(&[("X", "quantity"), ("Y", "quantity")]);
    let other_model = TraceModel::new(
        other,
        vec![state(&[("X", 1), ("Y", 1)]), state(&[("X", 2), ("Y", 0)])],
    )
    .unwrap();
    let law = derive_law(
        "A",
        "B",
        "quantity",
        [vec![q(-1)], vec![q(1)]],
        NullspaceSource::Incidence,
    );
    assert_eq!(
        ConservationInstitution.satisfies(&source, &other_model, &law),
        Err(Error::ModelSignatureMismatch)
    );
}
