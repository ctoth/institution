mod support;

use conservation_core::{AxisId, BalanceLaw, GradedLaw, Provenance};
use conservation_linear::{NullspaceSource, TransitionMatrix, derive_left_nullspace};
use conservation_trace::TraceState;
use institution::{Institution, laws};
use institution_conservation::{AxisRenaming, ConservationSignature, Error, TraceModel};
use num_bigint::BigInt;
use num_rational::BigRational;
use support::{CONSERVATION, FixtureKind};

fn axis(value: &str) -> AxisId {
    AxisId::new(value).unwrap()
}

fn q(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn signature(entries: &[(&str, FixtureKind)]) -> ConservationSignature<FixtureKind> {
    ConservationSignature::new(
        entries
            .iter()
            .map(|(axis_name, kind)| (axis(axis_name), *kind)),
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
    kind: FixtureKind,
    rows: [Vec<BigRational>; 2],
    source: NullspaceSource,
) -> BalanceLaw<FixtureKind> {
    let matrix = TransitionMatrix::new([axis(left), axis(right)], rows.to_vec()).unwrap();
    derive_left_nullspace(&matrix, kind, source)
        .unwrap()
        .into_iter()
        .next()
        .unwrap()
}

struct SharedCases {
    source: ConservationSignature<FixtureKind>,
    law: GradedLaw<FixtureKind>,
    ecological_renaming: AxisRenaming<FixtureKind>,
    ecological_model: TraceModel<FixtureKind>,
    economic_renaming: AxisRenaming<FixtureKind>,
    economic_model: TraceModel<FixtureKind>,
}

fn shared_neutral_cases() -> SharedCases {
    let source = signature(&[
        ("neutral_left", FixtureKind::NeutralQuantity),
        ("neutral_right", FixtureKind::NeutralQuantity),
    ]);
    // One exact directed incidence edge gives the neutral law [1, 1].
    let law = GradedLaw::from(derive_law(
        "neutral_left",
        "neutral_right",
        FixtureKind::NeutralQuantity,
        [vec![q(-1)], vec![q(1)]],
        NullspaceSource::Incidence,
    ));

    let ecological_target = signature(&[
        ("consumer_pool", FixtureKind::Biomass),
        ("producer_pool", FixtureKind::Biomass),
    ]);
    let ecological_renaming = AxisRenaming::new(
        source.clone(),
        ecological_target.clone(),
        [
            (axis("neutral_left"), axis("consumer_pool")),
            (axis("neutral_right"), axis("producer_pool")),
        ],
        [(FixtureKind::NeutralQuantity, FixtureKind::Biomass)],
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

    let economic_target = signature(&[
        ("asset_account", FixtureKind::Money),
        ("stock_account", FixtureKind::Money),
    ]);
    let economic_renaming = AxisRenaming::new(
        source.clone(),
        economic_target.clone(),
        [
            (axis("neutral_left"), axis("asset_account")),
            (axis("neutral_right"), axis("stock_account")),
        ],
        [(FixtureKind::NeutralQuantity, FixtureKind::Money)],
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
    let institution = CONSERVATION;

    assert_eq!(cases.ecological_renaming.source(), &cases.source);
    assert_eq!(cases.economic_renaming.source(), &cases.source);
    assert_eq!(
        cases.law.form().provenance(),
        &Provenance::IncidenceNullspace
    );
    let economic_source_law = cases.law.clone();
    assert_eq!(economic_source_law, cases.law);

    let ecological_law = institution
        .translate_sentence(&cases.ecological_renaming, &cases.law)
        .unwrap();
    let economic_law = institution
        .translate_sentence(&cases.economic_renaming, &economic_source_law)
        .unwrap();
    assert_eq!(ecological_law.form().kind(), FixtureKind::Biomass);
    assert_eq!(economic_law.form().kind(), FixtureKind::Money);
    assert_eq!(ecological_law.grade(), cases.law.grade());
    assert_eq!(economic_law.grade(), cases.law.grade());
    assert_eq!(
        ecological_law.form().provenance(),
        cases.law.form().provenance()
    );
    assert_eq!(
        economic_law.form().provenance(),
        cases.law.form().provenance()
    );

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
    let source = signature(&[
        ("left", FixtureKind::Quantity),
        ("right", FixtureKind::Quantity),
    ]);
    // The exact stoichiometric column [2, -1] has left-nullspace basis [1, 2].
    let law = derive_law(
        "left",
        "right",
        FixtureKind::Quantity,
        [vec![q(2)], vec![q(-1)]],
        NullspaceSource::Stoichiometric,
    );
    assert_eq!(law.coefficient(&axis("left")), &q(1));
    assert_eq!(law.coefficient(&axis("right")), &q(2));
    assert_eq!(law.provenance(), &Provenance::StoichiometricNullspace);

    let target = signature(&[
        ("alpha", FixtureKind::Measure),
        ("zeta", FixtureKind::Measure),
    ]);
    let reversing = AxisRenaming::new(
        source.clone(),
        target.clone(),
        [(axis("left"), axis("zeta")), (axis("right"), axis("alpha"))],
        [(FixtureKind::Quantity, FixtureKind::Measure)],
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

    let translated = CONSERVATION
        .translate_sentence(&reversing, &GradedLaw::from(law))
        .unwrap();
    assert_eq!(translated.form().kind(), FixtureKind::Measure);
    assert_eq!(translated.form().coefficient(&axis("alpha")), &q(2));
    assert_eq!(translated.form().coefficient(&axis("zeta")), &q(1));

    let reduced = CONSERVATION.reduct(&reversing, &target_model).unwrap();
    assert_eq!(reduced.signature(), &source);
    assert_eq!(reduced.states()[0].value(&axis("left")), Some(&q(10)));
    assert_eq!(reduced.states()[0].value(&axis("right")), Some(&q(20)));
}

#[test]
fn provenance_tags_do_not_change_satisfaction_semantics() {
    let source = signature(&[
        ("left", FixtureKind::Quantity),
        ("right", FixtureKind::Quantity),
    ]);
    let derived = derive_law(
        "left",
        "right",
        FixtureKind::Quantity,
        [vec![q(2)], vec![q(-1)]],
        NullspaceSource::Stoichiometric,
    );
    let declared = BalanceLaw::new(
        derived.kind(),
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
    let derived = GradedLaw::from(derived);
    let declared = GradedLaw::from(declared);
    assert_eq!(
        CONSERVATION.satisfies(&source, &model, &derived),
        CONSERVATION.satisfies(&source, &model, &declared)
    );
    assert_eq!(CONSERVATION.satisfies(&source, &model, &derived), Ok(true));
}

#[test]
fn signatures_axis_maps_and_models_retain_their_validation() {
    assert_eq!(
        ConservationSignature::<FixtureKind>::new([]),
        Err(Error::EmptySignature)
    );
    assert_eq!(
        ConservationSignature::new([
            (axis("A"), FixtureKind::Quantity),
            (axis("A"), FixtureKind::Quantity),
        ]),
        Err(Error::DuplicateSignatureAxis(axis("A")))
    );

    let source = signature(&[("A", FixtureKind::Quantity), ("B", FixtureKind::Quantity)]);
    let target = signature(&[("X", FixtureKind::Measure), ("Y", FixtureKind::Measure)]);
    let kind_map = [(FixtureKind::Quantity, FixtureKind::Measure)];
    assert_eq!(
        AxisRenaming::new(
            source.clone(),
            target.clone(),
            [(axis("A"), axis("X"))],
            kind_map,
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
    let source = signature(&[("A", FixtureKind::Q1), ("B", FixtureKind::Q2)]);
    let target = signature(&[("X", FixtureKind::R1), ("Y", FixtureKind::R2)]);
    let axes = [(axis("A"), axis("X")), (axis("B"), axis("Y"))];

    assert_eq!(
        AxisRenaming::new(
            source.clone(),
            target.clone(),
            axes.clone(),
            [(FixtureKind::Q1, FixtureKind::R1)],
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
                (FixtureKind::Q1, FixtureKind::R1),
                (FixtureKind::Q2, FixtureKind::R2),
                (FixtureKind::Outside, FixtureKind::R1),
            ],
        ),
        Err(Error::KindMappingSourceOutsideSignature(
            FixtureKind::Outside
        ))
    );
    assert_eq!(
        AxisRenaming::new(
            source.clone(),
            target.clone(),
            axes.clone(),
            [
                (FixtureKind::Q1, FixtureKind::R1),
                (FixtureKind::Q2, FixtureKind::Outside),
            ],
        ),
        Err(Error::KindMappingTargetOutsideSignature(
            FixtureKind::Outside
        ))
    );
    assert_eq!(
        AxisRenaming::new(
            source.clone(),
            target.clone(),
            axes.clone(),
            [
                (FixtureKind::Q1, FixtureKind::R1),
                (FixtureKind::Q1, FixtureKind::R1),
            ],
        ),
        Err(Error::DuplicateSourceKind(FixtureKind::Q1))
    );
    assert!(matches!(
        AxisRenaming::new(
            source.clone(),
            target.clone(),
            axes.clone(),
            [
                (FixtureKind::Q1, FixtureKind::R1),
                (FixtureKind::Q1, FixtureKind::R2),
            ],
        ),
        Err(Error::ConflictingKindMapping { .. })
    ));
    assert_eq!(
        AxisRenaming::new(
            source.clone(),
            target.clone(),
            axes.clone(),
            [
                (FixtureKind::Q1, FixtureKind::R1),
                (FixtureKind::Q2, FixtureKind::R1),
            ],
        ),
        Err(Error::DuplicateTargetKind(FixtureKind::R1))
    );

    let target_with_extra_kind = signature(&[
        ("X", FixtureKind::R1),
        ("Y", FixtureKind::R1),
        ("Z", FixtureKind::R2),
    ]);
    let one_kind_source = signature(&[("A", FixtureKind::Q1), ("B", FixtureKind::Q1)]);
    assert_eq!(
        AxisRenaming::new(
            one_kind_source,
            target_with_extra_kind,
            [(axis("A"), axis("X")), (axis("B"), axis("Y"))],
            [(FixtureKind::Q1, FixtureKind::R1)],
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
            [
                (FixtureKind::Q1, FixtureKind::R1),
                (FixtureKind::Q2, FixtureKind::R2)
            ],
        ),
        Err(Error::AxisKindMappingMismatch { .. })
    ));
}

#[test]
fn malformed_memberships_error_instead_of_returning_false() {
    let source = signature(&[("A", FixtureKind::Quantity), ("B", FixtureKind::Quantity)]);
    let model = TraceModel::new(
        source.clone(),
        vec![state(&[("A", 1), ("B", 1)]), state(&[("A", 2), ("B", 0)])],
    )
    .unwrap();
    let outside_law = GradedLaw::from(
        BalanceLaw::new(
            FixtureKind::Quantity,
            [(axis("outside"), q(1))],
            Provenance::Declared,
        )
        .unwrap(),
    );
    assert_eq!(
        CONSERVATION.satisfies(&source, &model, &outside_law),
        Err(Error::SentenceAxisOutsideSignature(axis("outside")))
    );

    let other = signature(&[("X", FixtureKind::Quantity), ("Y", FixtureKind::Quantity)]);
    let other_model = TraceModel::new(
        other,
        vec![state(&[("X", 1), ("Y", 1)]), state(&[("X", 2), ("Y", 0)])],
    )
    .unwrap();
    let law = GradedLaw::from(derive_law(
        "A",
        "B",
        FixtureKind::Quantity,
        [vec![q(-1)], vec![q(1)]],
        NullspaceSource::Incidence,
    ));
    assert_eq!(
        CONSERVATION.satisfies(&source, &other_model, &law),
        Err(Error::ModelSignatureMismatch)
    );
}

#[test]
fn conservation_adapter_observes_signature_category_and_functor_laws() {
    let source = signature(&[("A", FixtureKind::Quantity), ("B", FixtureKind::Quantity)]);
    let middle = signature(&[("X", FixtureKind::Mass), ("Y", FixtureKind::Mass)]);
    let target = signature(&[("U", FixtureKind::Energy), ("V", FixtureKind::Energy)]);
    let last = signature(&[("I", FixtureKind::Currency), ("J", FixtureKind::Currency)]);
    let first = AxisRenaming::new(
        source.clone(),
        middle,
        [(axis("A"), axis("X")), (axis("B"), axis("Y"))],
        [(FixtureKind::Quantity, FixtureKind::Mass)],
    )
    .unwrap();
    let second = AxisRenaming::new(
        first.target().clone(),
        target.clone(),
        [(axis("X"), axis("U")), (axis("Y"), axis("V"))],
        [(FixtureKind::Mass, FixtureKind::Energy)],
    )
    .unwrap();
    let third = AxisRenaming::new(
        target.clone(),
        last,
        [(axis("U"), axis("I")), (axis("V"), axis("J"))],
        [(FixtureKind::Energy, FixtureKind::Currency)],
    )
    .unwrap();
    let law = GradedLaw::from(
        BalanceLaw::new(
            FixtureKind::Quantity,
            [(axis("A"), q(1)), (axis("B"), q(1))],
            Provenance::Declared,
        )
        .unwrap(),
    );
    let model = TraceModel::new(
        target.clone(),
        vec![state(&[("U", 3), ("V", 7)]), state(&[("U", 4), ("V", 6)])],
    )
    .unwrap();
    let institution = CONSERVATION;

    assert!(laws::check_signature_identity(&institution, &first).unwrap());
    assert!(laws::check_signature_associativity(&institution, &first, &second, &third,).unwrap());
    assert!(laws::check_sentence_identity(&institution, &source, &law).unwrap());
    assert!(laws::check_sentence_composition(&institution, &first, &second, &law,).unwrap());
    assert!(laws::check_model_identity(&institution, &target, &model).unwrap());
    assert!(laws::check_model_composition(&institution, &first, &second, &model,).unwrap());
}
