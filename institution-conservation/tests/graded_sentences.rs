//! Satisfaction squares for the nonnegative and nondecreasing sentence grades.
//!
//! One neutral signature carries three graded sentences — an invariant total,
//! a nonnegative reservoir, and a nondecreasing dissipation axis — and is
//! renamed into a weather ledger (Lorenz-style energy reservoirs) and an
//! ecological ledger. The weather model satisfies all three grades; the
//! ecological model conserves its total while violating both inequalities, so
//! every square is exercised in both outcomes.

mod support;

use conservation_core::{AxisId, BalanceLaw, Grade, GradedLaw, Provenance};
use conservation_trace::TraceState;
use institution::{Institution, laws};
use institution_conservation::{AxisRenaming, ConservationSignature, TraceModel};
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

fn graded(kind: FixtureKind, coefficients: &[(&str, i64)], grade: Grade) -> GradedLaw<FixtureKind> {
    GradedLaw::new(
        BalanceLaw::new(
            kind,
            coefficients
                .iter()
                .map(|(axis_name, value)| (axis(axis_name), q(*value))),
            Provenance::Declared,
        )
        .unwrap(),
        grade,
    )
}

struct GradedCases {
    source: ConservationSignature<FixtureKind>,
    total: GradedLaw<FixtureKind>,
    reservoir: GradedLaw<FixtureKind>,
    dissipation: GradedLaw<FixtureKind>,
    weather_renaming: AxisRenaming<FixtureKind>,
    weather_model: TraceModel<FixtureKind>,
    ecological_renaming: AxisRenaming<FixtureKind>,
    ecological_model: TraceModel<FixtureKind>,
}

fn shared_graded_cases() -> GradedCases {
    let source = signature(&[
        ("upper_store", FixtureKind::NeutralEnergy),
        ("lower_store", FixtureKind::NeutralEnergy),
        ("dissipated", FixtureKind::NeutralEnergy),
    ]);
    let total = graded(
        FixtureKind::NeutralEnergy,
        &[("upper_store", 1), ("lower_store", 1), ("dissipated", 1)],
        Grade::Invariant,
    );
    let reservoir = graded(
        FixtureKind::NeutralEnergy,
        &[("lower_store", 1)],
        Grade::Nonnegative,
    );
    let dissipation = graded(
        FixtureKind::NeutralEnergy,
        &[("dissipated", 1)],
        Grade::Nondecreasing,
    );

    // The Lorenz reading: available potential energy converts to kinetic
    // energy, and friction moves both into a heat axis that only grows.
    let weather_target = signature(&[
        ("available_potential", FixtureKind::Energy),
        ("kinetic", FixtureKind::Energy),
        ("dissipated_heat", FixtureKind::Energy),
    ]);
    let weather_renaming = AxisRenaming::new(
        source.clone(),
        weather_target.clone(),
        [
            (axis("upper_store"), axis("available_potential")),
            (axis("lower_store"), axis("kinetic")),
            (axis("dissipated"), axis("dissipated_heat")),
        ],
        [(FixtureKind::NeutralEnergy, FixtureKind::Energy)],
    )
    .unwrap();
    let weather_model = TraceModel::new(
        weather_target,
        vec![
            state(&[
                ("available_potential", 10),
                ("kinetic", 0),
                ("dissipated_heat", 0),
            ]),
            state(&[
                ("available_potential", 6),
                ("kinetic", 3),
                ("dissipated_heat", 1),
            ]),
            state(&[
                ("available_potential", 2),
                ("kinetic", 5),
                ("dissipated_heat", 3),
            ]),
        ],
    )
    .unwrap();

    // A corrupted ecological ledger: total biomass energy balances, but the
    // consumer pool dips negative and respiration runs backwards.
    let ecological_target = signature(&[
        ("producer_pool", FixtureKind::BiomassEnergy),
        ("consumer_pool", FixtureKind::BiomassEnergy),
        ("respired", FixtureKind::BiomassEnergy),
    ]);
    let ecological_renaming = AxisRenaming::new(
        source.clone(),
        ecological_target.clone(),
        [
            (axis("upper_store"), axis("producer_pool")),
            (axis("lower_store"), axis("consumer_pool")),
            (axis("dissipated"), axis("respired")),
        ],
        [(FixtureKind::NeutralEnergy, FixtureKind::BiomassEnergy)],
    )
    .unwrap();
    let ecological_model = TraceModel::new(
        ecological_target,
        vec![
            state(&[("producer_pool", 5), ("consumer_pool", 1), ("respired", 4)]),
            state(&[("producer_pool", 7), ("consumer_pool", -1), ("respired", 4)]),
            state(&[("producer_pool", 6), ("consumer_pool", 1), ("respired", 3)]),
        ],
    )
    .unwrap();

    GradedCases {
        source,
        total,
        reservoir,
        dissipation,
        weather_renaming,
        weather_model,
        ecological_renaming,
        ecological_model,
    }
}

#[test]
fn translation_preserves_every_grade() {
    let cases = shared_graded_cases();
    let institution = CONSERVATION;

    for sentence in [&cases.total, &cases.reservoir, &cases.dissipation] {
        let translated = institution
            .translate_sentence(&cases.weather_renaming, sentence)
            .unwrap();
        assert_eq!(translated.grade(), sentence.grade());
        assert_eq!(translated.form().kind(), FixtureKind::Energy);
        assert_eq!(translated.form().provenance(), sentence.form().provenance());
    }
}

#[test]
fn weather_squares_hold_true_for_all_three_grades() {
    let cases = shared_graded_cases();
    let institution = CONSERVATION;

    for sentence in [&cases.total, &cases.reservoir, &cases.dissipation] {
        let square = laws::check_satisfaction_square(
            &institution,
            &cases.weather_renaming,
            sentence,
            &cases.weather_model,
        )
        .unwrap();
        assert!(square.holds());
        assert!(square.translated_sentence_satisfied());
        assert!(square.reduced_model_satisfies_source_sentence());
    }
}

#[test]
fn corrupted_ecological_squares_hold_with_false_inequality_grades() {
    let cases = shared_graded_cases();
    let institution = CONSERVATION;

    // The balanced total still holds: corruption hid inside conserved books.
    let invariant_square = laws::check_satisfaction_square(
        &institution,
        &cases.ecological_renaming,
        &cases.total,
        &cases.ecological_model,
    )
    .unwrap();
    assert!(invariant_square.holds());
    assert!(invariant_square.translated_sentence_satisfied());

    for sentence in [&cases.reservoir, &cases.dissipation] {
        let square = laws::check_satisfaction_square(
            &institution,
            &cases.ecological_renaming,
            sentence,
            &cases.ecological_model,
        )
        .unwrap();
        assert!(square.holds());
        assert!(!square.translated_sentence_satisfied());
        assert!(!square.reduced_model_satisfies_source_sentence());
    }
}

#[test]
fn graded_satisfaction_is_non_vacuous_across_both_targets() {
    let cases = shared_graded_cases();
    let institution = CONSERVATION;

    let weather_sentences = [&cases.total, &cases.reservoir, &cases.dissipation].map(|sentence| {
        institution
            .translate_sentence(&cases.weather_renaming, sentence)
            .unwrap()
    });
    let ecological_sentences =
        [&cases.total, &cases.reservoir, &cases.dissipation].map(|sentence| {
            institution
                .translate_sentence(&cases.ecological_renaming, sentence)
                .unwrap()
        });

    let mut examples = Vec::new();
    for sentence in &weather_sentences {
        examples.push((
            cases.weather_renaming.target(),
            &cases.weather_model,
            sentence,
        ));
    }
    for sentence in &ecological_sentences {
        examples.push((
            cases.ecological_renaming.target(),
            &cases.ecological_model,
            sentence,
        ));
    }

    let evidence = laws::check_non_vacuity(&institution, examples).unwrap();
    assert!(evidence.is_non_vacuous());
    assert_eq!(evidence.satisfying_cases(), 4);
    assert_eq!(evidence.falsifying_cases(), 2);
}

#[test]
fn graded_sentences_observe_the_sentence_functor_laws() {
    let cases = shared_graded_cases();
    let institution = CONSERVATION;

    let onward = signature(&[
        ("alpha", FixtureKind::Measure),
        ("beta", FixtureKind::Measure),
        ("gamma", FixtureKind::Measure),
    ]);
    let second = AxisRenaming::new(
        cases.weather_renaming.target().clone(),
        onward,
        [
            (axis("available_potential"), axis("alpha")),
            (axis("kinetic"), axis("beta")),
            (axis("dissipated_heat"), axis("gamma")),
        ],
        [(FixtureKind::Energy, FixtureKind::Measure)],
    )
    .unwrap();

    for sentence in [&cases.total, &cases.reservoir, &cases.dissipation] {
        assert!(laws::check_sentence_identity(&institution, &cases.source, sentence).unwrap());
        assert!(
            laws::check_sentence_composition(
                &institution,
                &cases.weather_renaming,
                &second,
                sentence,
            )
            .unwrap()
        );
    }
}
