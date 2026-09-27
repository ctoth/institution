mod support;

use conservation_core::{AxisId, BalanceLaw, GradedLaw, Provenance};
use conservation_linear::{NullspaceSource, TransitionMatrix, derive_left_nullspace};
use conservation_trace::LawVerdict;
use conservation_trace::TraceState;
use institution::{Institution, laws};
use institution::{Renaming, RenamingError};
use institution_conservation::{
    ConservationInstitution, ConservationSignature, Error, KindConflict, TraceModel,
};
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
    ecological_renaming: Renaming<ConservationSignature<FixtureKind>>,
    ecological_model: TraceModel<FixtureKind>,
    economic_renaming: Renaming<ConservationSignature<FixtureKind>>,
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
    let ecological_renaming = Renaming::new(
        source.clone(),
        ecological_target.clone(),
        [
            (axis("neutral_left"), axis("consumer_pool")),
            (axis("neutral_right"), axis("producer_pool")),
        ],
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
    let economic_renaming = Renaming::new(
        source.clone(),
        economic_target.clone(),
        [
            (axis("neutral_left"), axis("asset_account")),
            (axis("neutral_right"), axis("stock_account")),
        ],
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
    let reversing = Renaming::new(
        source.clone(),
        target.clone(),
        [(axis("left"), axis("zeta")), (axis("right"), axis("alpha"))],
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
    assert_eq!(
        Renaming::new(source.clone(), target.clone(), [(axis("A"), axis("X"))]),
        Err(Error::Renaming(RenamingError::Unnamed(axis("B"))))
    );
    assert_eq!(
        Renaming::new(
            source.clone(),
            target,
            [(axis("A"), axis("X")), (axis("B"), axis("X"))],
        ),
        Err(Error::Renaming(RenamingError::NotInjective(axis("X"))))
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
fn the_kind_map_is_derived_from_the_axis_map() {
    let source = signature(&[("A", FixtureKind::Q1), ("B", FixtureKind::Q1)]);
    let target = signature(&[
        ("X", FixtureKind::Mass),
        ("Y", FixtureKind::Energy),
        ("Z", FixtureKind::Mass),
    ]);
    assert_eq!(
        Renaming::new(
            source.clone(),
            target.clone(),
            [(axis("A"), axis("X")), (axis("B"), axis("Y"))],
        ),
        Err(Error::KindConflict(KindConflict {
            symbol: axis("B"),
            kind: FixtureKind::Q1,
            first: FixtureKind::Mass,
            second: FixtureKind::Energy,
        }))
    );

    let renaming = Renaming::new(
        source,
        target,
        [(axis("A"), axis("X")), (axis("B"), axis("Z"))],
    )
    .unwrap();
    let law = GradedLaw::from(
        BalanceLaw::new(FixtureKind::Q1, [(axis("A"), q(1))], Provenance::Declared).unwrap(),
    );
    assert_eq!(
        CONSERVATION
            .translate_sentence(&renaming, &law)
            .unwrap()
            .form()
            .kind(),
        FixtureKind::Mass
    );

    // Two kinds may share an image; the map need not be injective.
    assert!(
        Renaming::new(
            signature(&[("A", FixtureKind::Q1), ("B", FixtureKind::Q2)]),
            signature(&[("X", FixtureKind::Mass), ("Y", FixtureKind::Mass)]),
            [(axis("A"), axis("X")), (axis("B"), axis("Y"))],
        )
        .is_ok()
    );
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
    let first = Renaming::new(
        source.clone(),
        middle,
        [(axis("A"), axis("X")), (axis("B"), axis("Y"))],
    )
    .unwrap();
    let second = Renaming::new(
        first.target().clone(),
        target.clone(),
        [(axis("X"), axis("U")), (axis("Y"), axis("V"))],
    )
    .unwrap();
    let third = Renaming::new(
        target.clone(),
        last,
        [(axis("U"), axis("I")), (axis("V"), axis("J"))],
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

fn two_axes() -> ConservationSignature<FixtureKind> {
    signature(&[("A", FixtureKind::Quantity), ("B", FixtureKind::Quantity)])
}

fn three_axes() -> ConservationSignature<FixtureKind> {
    signature(&[
        ("X", FixtureKind::Mass),
        ("Y", FixtureKind::Mass),
        ("Z", FixtureKind::Mass),
    ])
}

/// Renames `A` and `B` into `X` and `Y`, forgetting `Z`.
fn forgetting_z() -> Renaming<ConservationSignature<FixtureKind>> {
    Renaming::new(
        two_axes(),
        three_axes(),
        [(axis("A"), axis("X")), (axis("B"), axis("Y"))],
    )
    .unwrap()
}

fn total_of_a_and_b() -> GradedLaw<FixtureKind> {
    GradedLaw::from(
        BalanceLaw::new(
            FixtureKind::Quantity,
            [(axis("A"), q(1)), (axis("B"), q(1))],
            Provenance::Declared,
        )
        .unwrap(),
    )
}

/// `X + Y` is constant while the forgotten `Z` jumps.
fn z_jumps() -> TraceModel<FixtureKind> {
    TraceModel::new(
        three_axes(),
        vec![
            state(&[("X", 3), ("Y", 7), ("Z", 0)]),
            state(&[("X", 4), ("Y", 6), ("Z", 50)]),
        ],
    )
    .unwrap()
}

#[test]
fn forgetting_an_axis_keeps_the_square_with_both_truth_values() {
    let renaming = forgetting_z();
    let law = total_of_a_and_b();

    let reduced = CONSERVATION.reduct(&renaming, &z_jumps()).unwrap();
    assert_eq!(reduced.signature(), &two_axes());
    assert_eq!(reduced.states()[1].axes().count(), 2);

    let kept = laws::check_satisfaction_square(&CONSERVATION, &renaming, &law, &z_jumps()).unwrap();
    assert!(kept.holds());
    assert!(kept.translated_sentence_satisfied());

    let leaking = TraceModel::new(
        three_axes(),
        vec![
            state(&[("X", 3), ("Y", 7), ("Z", 0)]),
            state(&[("X", 4), ("Y", 7), ("Z", 0)]),
        ],
    )
    .unwrap();
    let broken = laws::check_satisfaction_square(&CONSERVATION, &renaming, &law, &leaking).unwrap();
    assert!(broken.holds());
    assert!(!broken.translated_sentence_satisfied());
}

/// The conservation institution, except that sentences translate along a
/// renaming that sends `B` to the forgotten `Z`.
struct TranslatesIntoZ;

impl Institution for TranslatesIntoZ {
    type Signature = ConservationSignature<FixtureKind>;
    type SignatureMorphism = Renaming<ConservationSignature<FixtureKind>>;
    type Sentence = GradedLaw<FixtureKind>;
    type Model = TraceModel<FixtureKind>;
    type Error = Error<FixtureKind>;

    fn source<'a>(&self, morphism: &'a Self::SignatureMorphism) -> &'a Self::Signature {
        CONSERVATION.source(morphism)
    }

    fn target<'a>(&self, morphism: &'a Self::SignatureMorphism) -> &'a Self::Signature {
        CONSERVATION.target(morphism)
    }

    fn identity(
        &self,
        signature: &Self::Signature,
    ) -> Result<Self::SignatureMorphism, Self::Error> {
        CONSERVATION.identity(signature)
    }

    fn compose(
        &self,
        first: &Self::SignatureMorphism,
        second: &Self::SignatureMorphism,
    ) -> Result<Self::SignatureMorphism, Self::Error> {
        CONSERVATION.compose(first, second)
    }

    fn translate_sentence(
        &self,
        morphism: &Self::SignatureMorphism,
        sentence: &Self::Sentence,
    ) -> Result<Self::Sentence, Self::Error> {
        let stale = Renaming::new(
            morphism.source().clone(),
            morphism.target().clone(),
            [(axis("A"), axis("X")), (axis("B"), axis("Z"))],
        )?;
        CONSERVATION.translate_sentence(&stale, sentence)
    }

    fn reduct(
        &self,
        morphism: &Self::SignatureMorphism,
        model: &Self::Model,
    ) -> Result<Self::Model, Self::Error> {
        CONSERVATION.reduct(morphism, model)
    }

    fn satisfies(
        &self,
        signature: &Self::Signature,
        model: &Self::Model,
        sentence: &Self::Sentence,
    ) -> Result<bool, Self::Error> {
        CONSERVATION.satisfies(signature, model, sentence)
    }
}

#[test]
fn a_translation_into_the_forgotten_axis_breaks_the_square() {
    let square = laws::check_satisfaction_square(
        &TranslatesIntoZ,
        &forgetting_z(),
        &total_of_a_and_b(),
        &z_jumps(),
    )
    .unwrap();
    assert!(!square.holds());
    assert!(!square.translated_sentence_satisfied());
    assert!(square.reduced_model_satisfies_source_sentence());
}

#[test]
fn evaluation_returns_the_verdict_satisfaction_reads() {
    let law = total_of_a_and_b();
    let holding = CONSERVATION.reduct(&forgetting_z(), &z_jumps()).unwrap();
    let leaking = TraceModel::new(
        two_axes(),
        vec![state(&[("A", 3), ("B", 7)]), state(&[("A", 4), ("B", 7)])],
    )
    .unwrap();

    assert!(matches!(
        ConservationInstitution::evaluate(&law, &holding),
        Ok(LawVerdict::Satisfied(_))
    ));
    assert_eq!(
        CONSERVATION.satisfies(&two_axes(), &holding, &law),
        Ok(true)
    );
    assert!(matches!(
        ConservationInstitution::evaluate(&law, &leaking),
        Ok(LawVerdict::Violated(_))
    ));
    assert_eq!(
        CONSERVATION.satisfies(&two_axes(), &leaking, &law),
        Ok(false)
    );
}
