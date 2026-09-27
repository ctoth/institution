mod support;

use conservation_core::{BalanceLaw, Grade, GradedLaw, Provenance};
use std::sync::Arc;

use conservation_dynamics::{FlowTopology, StockDefinition, StockId};
use conservation_stock_flow::{
    BoundaryCorrespondence, GradedStateLaw, LinearFlowConstraint, StockAxisDefinition,
    StockFlowCarrier, StockFlowError, Symbol, SymbolId, TransitionEquation, TransitionRecord,
    certify_nullspace,
};
use institution::{Institution, Renaming, RenamingError, laws};
use institution_conservation::KindConflict;
use institution_conservation::stock_flow::{
    Error, StockFlowInstitution, StockFlowModel, StockFlowSentence, StockFlowSignature,
};
use proptest::prelude::*;
use support::*;

#[test]
fn every_sentence_family_has_true_and_false_semantic_evidence() {
    let signature = signature(NEUTRAL);
    let valid = valid_model(&signature, NEUTRAL);
    for sentence in sentences(&signature, NEUTRAL) {
        assert!(
            StockFlowInstitution::evaluate(&sentence, &valid)
                .unwrap()
                .is_satisfied()
        );
    }

    let invalid_equation = model_with_values(&signature, NEUTRAL, -2, 12, 3, 2, 1, false, true);
    let invalid_ledger = model_with_values(&signature, NEUTRAL, -2, 12, 3, 2, 1, true, false);
    let false_linear = StockFlowSentence::LinearFlow(
        LinearFlowConstraint::new(
            signature.carrier(),
            sentence("false-linear"),
            NEUTRAL.kind,
            [(flow(NEUTRAL.flow), q(1))],
            q(4),
        )
        .unwrap(),
    );
    let false_graded = StockFlowSentence::Graded(GradedStateLaw::new(
        sentence("false-graded"),
        GradedLaw::new(
            BalanceLaw::new(
                NEUTRAL.kind,
                [(axis(NEUTRAL.left_axis), q(1))],
                Provenance::Declared,
            )
            .unwrap(),
            Grade::Nonnegative,
        ),
    ));
    let all = sentences(&signature, NEUTRAL);
    let false_cases = [
        (&all[0], &invalid_equation),
        (&false_linear, &valid),
        (&all[2], &invalid_ledger),
        (&false_graded, &valid),
        (&all[4], &invalid_equation),
    ];
    for (sentence, model) in false_cases {
        assert!(
            !StockFlowInstitution::evaluate(sentence, model)
                .unwrap()
                .is_satisfied()
        );
    }
}

#[test]
fn all_category_functor_and_satisfaction_laws_hold_for_every_family() {
    let source = signature(NEUTRAL);
    let middle = signature(ECOLOGY);
    let target = signature(ECONOMY);
    let last = signature(FOURTH);
    let first = renaming(NEUTRAL, source.clone(), ECOLOGY, middle);
    let second = renaming(ECOLOGY, first.target().clone(), ECONOMY, target.clone());
    let third = renaming(ECONOMY, target.clone(), FOURTH, last);
    let target_model = valid_model(&target, ECONOMY);
    let institution = STOCK_FLOW;

    assert!(laws::check_signature_identity(&institution, &first).unwrap());
    assert!(laws::check_signature_associativity(&institution, &first, &second, &third).unwrap());
    assert!(laws::check_model_identity(&institution, &target, &target_model).unwrap());
    assert!(laws::check_model_composition(&institution, &first, &second, &target_model).unwrap());

    for sentence in sentences(&source, NEUTRAL) {
        assert!(laws::check_sentence_identity(&institution, &source, &sentence).unwrap());
        assert!(
            laws::check_sentence_composition(&institution, &first, &second, &sentence).unwrap()
        );
        let square = laws::check_satisfaction_square(
            &institution,
            &first,
            &sentence,
            &valid_model(first.target(), ECOLOGY),
        )
        .unwrap();
        assert!(square.holds());
        assert!(square.translated_sentence_satisfied());
    }
}

#[test]
fn every_sentence_family_preserves_false_satisfaction_through_reduct() {
    let source = signature(NEUTRAL);
    let morphism = renaming(NEUTRAL, source.clone(), ECOLOGY, signature(ECOLOGY));
    let source_sentences = sentences(&source, NEUTRAL);
    let false_models = [
        model_with_values(morphism.target(), ECOLOGY, -2, 12, 3, 2, 1, false, true),
        model_with_values(morphism.target(), ECOLOGY, -2, 12, 4, 2, 1, true, true),
        model_with_values(morphism.target(), ECOLOGY, -2, 12, 3, 2, 1, true, false),
        model_with_values(morphism.target(), ECOLOGY, -2, 12, 3, 2, 1, false, true),
        model_with_values(morphism.target(), ECOLOGY, -2, 12, 3, 2, 1, false, true),
    ];

    for (sentence, target_model) in source_sentences.iter().zip(&false_models) {
        let square =
            laws::check_satisfaction_square(&STOCK_FLOW, &morphism, sentence, target_model)
                .unwrap();
        assert!(square.holds());
        assert!(!square.translated_sentence_satisfied());
        assert!(!square.reduced_model_satisfies_source_sentence());
    }
}

#[test]
fn one_neutral_stock_flow_spec_instantiates_ecological_and_economic_models() {
    let source = signature(NEUTRAL);
    let ecological = renaming(NEUTRAL, source.clone(), ECOLOGY, signature(ECOLOGY));
    let economic = renaming(NEUTRAL, source.clone(), ECONOMY, signature(ECONOMY));
    for sentence in sentences(&source, NEUTRAL) {
        for (morphism, model) in [
            (&ecological, valid_model(ecological.target(), ECOLOGY)),
            (&economic, valid_model(economic.target(), ECONOMY)),
        ] {
            let square =
                laws::check_satisfaction_square(&STOCK_FLOW, morphism, &sentence, &model).unwrap();
            assert!(square.holds());
            assert!(square.translated_sentence_satisfied());
        }
    }
}

#[test]
fn malformed_morphisms_and_model_membership_are_rejected() {
    let source = signature(NEUTRAL);
    let target = signature(ECOLOGY);
    let mut without_output_axis = shared_pairs(NEUTRAL, ECOLOGY);
    without_output_axis.push((
        ledger(NEUTRAL.output_ledger).symbol_id(),
        ledger(ECOLOGY.output_ledger).symbol_id(),
    ));
    assert_eq!(
        Renaming::new(source.clone(), target.clone(), without_output_axis),
        Err(Error::Renaming(RenamingError::Unnamed(
            axis(NEUTRAL.output_ledger_axis).symbol_id()
        )))
    );
    let target_model = valid_model(&target, ECOLOGY);
    assert_eq!(
        STOCK_FLOW.satisfies(&source, &target_model, &sentences(&source, NEUTRAL)[0]),
        Err(Error::ModelSignatureMismatch)
    );

    let valid_renaming = renaming(NEUTRAL, source.clone(), ECOLOGY, target);
    let outside = StockFlowSentence::Graded(GradedStateLaw::new(
        sentence("outside-axis"),
        GradedLaw::from(
            BalanceLaw::new(
                NEUTRAL.kind,
                [(axis("outside"), q(1))],
                Provenance::Declared,
            )
            .unwrap(),
        ),
    ));
    assert!(matches!(
        STOCK_FLOW.translate_sentence(&valid_renaming, &outside),
        Err(Error::Carrier(StockFlowError::UnknownAxis(_)))
    ));

    let other = signature(ECONOMY);
    let foreign_certificate = certify_nullspace(
        other.carrier(),
        ECONOMY.kind,
        [
            (axis(ECONOMY.left_axis), q(1)),
            (axis(ECONOMY.right_axis), q(1)),
        ],
    )
    .unwrap();
    let foreign = StockFlowSentence::OpenBalance(
        foreign_certificate.open_balance(sentence("foreign-certificate")),
    );
    assert_eq!(
        STOCK_FLOW.translate_sentence(&valid_renaming, &foreign),
        Err(Error::Carrier(StockFlowError::CarrierMismatch))
    );
}

#[test]
fn signed_observations_are_valid_but_negative_flow_magnitudes_are_rejected() {
    let signature = signature(NEUTRAL);
    let valid = valid_model(&signature, NEUTRAL);
    assert_eq!(
        valid.trace().records()[0]
            .before()
            .amount(&axis(NEUTRAL.left_axis)),
        Some(&q(-2))
    );
    assert_eq!(
        valid.trace().records()[0]
            .ledger_before()
            .amount(&ledger(NEUTRAL.output_ledger)),
        Some(&q(-5))
    );

    let mut data = valid.trace().records()[0].clone().into_data();
    data.requested_internal = amounts([(flow(NEUTRAL.flow), NEUTRAL.kind, q(-1))]);
    assert_eq!(
        TransitionRecord::new(signature.carrier(), data),
        Err(StockFlowError::NegativeAmount(SymbolId::Flow(flow(
            NEUTRAL.flow
        ))))
    );
}

/// One sentence of each family over the input-ledger-only carrier of `names`.
fn input_ledger_sentences(
    signature: &StockFlowSignature<FixtureKind>,
    names: Names,
) -> Vec<StockFlowSentence<FixtureKind>> {
    let certificate = certify_nullspace(
        signature.carrier(),
        names.kind,
        [
            (axis(names.left_axis), q(1)),
            (axis(names.right_axis), q(1)),
        ],
    )
    .unwrap();
    vec![
        StockFlowSentence::Transition(TransitionEquation::new(sentence("transition"))),
        StockFlowSentence::LinearFlow(
            LinearFlowConstraint::new(
                signature.carrier(),
                sentence("linear-flow"),
                names.kind,
                [(flow(names.flow), q(1))],
                q(3),
            )
            .unwrap(),
        ),
        StockFlowSentence::Boundary(BoundaryCorrespondence::new(
            sentence("boundary"),
            ledger(names.input_ledger),
        )),
        StockFlowSentence::Graded(GradedStateLaw::new(
            sentence("graded"),
            GradedLaw::new(
                BalanceLaw::new(
                    names.kind,
                    [
                        (axis(names.right_axis), q(1)),
                        (axis(names.input_ledger_axis), q(1)),
                    ],
                    Provenance::Declared,
                )
                .unwrap(),
                Grade::Nonnegative,
            ),
        )),
        StockFlowSentence::OpenBalance(certificate.open_balance(sentence("open-balance"))),
    ]
}

/// A carrier of unconnected stocks, one axis per stock.
fn stocks(entries: &[(&str, FixtureKind)]) -> StockFlowSignature<FixtureKind> {
    let topology = FlowTopology::new(
        entries.iter().map(|(name, kind)| StockDefinition {
            id: StockId::new(*name).unwrap(),
            kind: *kind,
        }),
        [],
        [],
    )
    .unwrap();
    let carrier = StockFlowCarrier::new(
        Arc::new(topology),
        entries.iter().map(|(name, _)| StockAxisDefinition {
            stock: StockId::new(*name).unwrap(),
            axis: axis(name),
        }),
        [],
        [],
    )
    .unwrap();
    StockFlowSignature::new(Arc::new(carrier))
}

#[test]
fn forgetting_a_ledger_keeps_every_square_with_both_truth_values() {
    let morphism = forgetting_renaming(NEUTRAL, ECOLOGY);
    let target = morphism.target().clone();
    let drifted = with_output_ledger_drift(&valid_model(&target, ECOLOGY), ECOLOGY, 7);

    // The drift is visible at the target and invisible after the reduct.
    assert!(
        !STOCK_FLOW
            .satisfies(
                &target,
                &drifted,
                &StockFlowSentence::Boundary(BoundaryCorrespondence::new(
                    sentence("output"),
                    ledger(ECOLOGY.output_ledger),
                )),
            )
            .unwrap()
    );
    assert_eq!(
        STOCK_FLOW.reduct(&morphism, &drifted).unwrap(),
        STOCK_FLOW
            .reduct(&morphism, &valid_model(&target, ECOLOGY))
            .unwrap()
    );

    let false_models = [
        model_with_values(&target, ECOLOGY, -2, 12, 3, 2, 1, false, true),
        model_with_values(&target, ECOLOGY, -2, 12, 4, 2, 1, true, true),
        model_with_values(&target, ECOLOGY, -2, 12, 3, 2, 1, true, false),
        model_with_values(&target, ECOLOGY, -2, -12, 3, 2, 1, true, true),
        model_with_values(&target, ECOLOGY, -2, 12, 3, 2, 1, false, true),
    ];
    let source_sentences = input_ledger_sentences(morphism.source(), NEUTRAL);
    for (sentence, false_model) in source_sentences.iter().zip(&false_models) {
        let kept =
            laws::check_satisfaction_square(&STOCK_FLOW, &morphism, sentence, &drifted).unwrap();
        assert!(kept.holds());
        assert!(kept.translated_sentence_satisfied());

        let broken =
            laws::check_satisfaction_square(&STOCK_FLOW, &morphism, sentence, false_model).unwrap();
        assert!(broken.holds());
        assert!(!broken.translated_sentence_satisfied());
    }
}

/// Stock-flow, except that a translated boundary sentence reads the target's
/// output ledger, which the forgetting renaming leaves out.
struct ReadsForgottenLedger;

impl Institution for ReadsForgottenLedger {
    type Signature = StockFlowSignature<FixtureKind>;
    type SignatureMorphism = Renaming<StockFlowSignature<FixtureKind>>;
    type Sentence = StockFlowSentence<FixtureKind>;
    type Model = StockFlowModel<FixtureKind>;
    type Error = Error<FixtureKind>;

    fn source<'a>(&self, morphism: &'a Self::SignatureMorphism) -> &'a Self::Signature {
        STOCK_FLOW.source(morphism)
    }

    fn target<'a>(&self, morphism: &'a Self::SignatureMorphism) -> &'a Self::Signature {
        STOCK_FLOW.target(morphism)
    }

    fn identity(
        &self,
        signature: &Self::Signature,
    ) -> Result<Self::SignatureMorphism, Self::Error> {
        STOCK_FLOW.identity(signature)
    }

    fn compose(
        &self,
        first: &Self::SignatureMorphism,
        second: &Self::SignatureMorphism,
    ) -> Result<Self::SignatureMorphism, Self::Error> {
        STOCK_FLOW.compose(first, second)
    }

    fn translate_sentence(
        &self,
        morphism: &Self::SignatureMorphism,
        sentence: &Self::Sentence,
    ) -> Result<Self::Sentence, Self::Error> {
        Ok(match STOCK_FLOW.translate_sentence(morphism, sentence)? {
            StockFlowSentence::Boundary(translated) => StockFlowSentence::Boundary(
                BoundaryCorrespondence::new(translated.id().clone(), ledger(ECOLOGY.output_ledger)),
            ),
            translated => translated,
        })
    }

    fn reduct(
        &self,
        morphism: &Self::SignatureMorphism,
        model: &Self::Model,
    ) -> Result<Self::Model, Self::Error> {
        STOCK_FLOW.reduct(morphism, model)
    }

    fn satisfies(
        &self,
        signature: &Self::Signature,
        model: &Self::Model,
        sentence: &Self::Sentence,
    ) -> Result<bool, Self::Error> {
        STOCK_FLOW.satisfies(signature, model, sentence)
    }
}

#[test]
fn a_translation_that_reads_the_forgotten_ledger_breaks_the_square() {
    let morphism = forgetting_renaming(NEUTRAL, ECOLOGY);
    let drifted = with_output_ledger_drift(&valid_model(morphism.target(), ECOLOGY), ECOLOGY, 7);
    let boundary = StockFlowSentence::Boundary(BoundaryCorrespondence::new(
        sentence("boundary"),
        ledger(NEUTRAL.input_ledger),
    ));

    let square =
        laws::check_satisfaction_square(&ReadsForgottenLedger, &morphism, &boundary, &drifted)
            .unwrap();
    assert!(!square.holds());
    assert!(!square.translated_sentence_satisfied());
    assert!(square.reduced_model_satisfies_source_sentence());
}

#[test]
fn a_renaming_may_forget_ledgers_but_not_what_the_transition_equation_reads() {
    let source = stocks(&[("a", FixtureKind::Quantity)]);
    let target = stocks(&[("a", FixtureKind::Quantity), ("b", FixtureKind::Quantity)]);
    assert_eq!(
        Renaming::new(
            source,
            target,
            [(axis("a").symbol_id(), axis("a").symbol_id())]
        ),
        Err(Error::Forgotten(axis("b").symbol_id()))
    );
}

#[test]
fn a_renaming_keeps_classes_incidence_and_one_derived_kind_map() {
    let source = signature_with(NEUTRAL, false);
    let target = signature(ECOLOGY);
    let crossed = shared_pairs(NEUTRAL, ECOLOGY)
        .into_iter()
        .map(|(from, to)| {
            if to == flow(ECOLOGY.flow).symbol_id() {
                (from, boundary(ECOLOGY.input).symbol_id())
            } else if to == boundary(ECOLOGY.input).symbol_id() {
                (from, flow(ECOLOGY.flow).symbol_id())
            } else {
                (from, to)
            }
        });
    assert_eq!(
        Renaming::new(source.clone(), target.clone(), crossed),
        Err(Error::ClassChanged {
            source: flow(NEUTRAL.flow).symbol_id(),
            target: boundary(ECOLOGY.input).symbol_id(),
        })
    );

    let swapped = [
        (axis(NEUTRAL.left_axis), axis(ECOLOGY.right_axis)),
        (axis(NEUTRAL.right_axis), axis(ECOLOGY.left_axis)),
    ];
    let mut reversed = shared_pairs(NEUTRAL, ECOLOGY)
        .into_iter()
        .skip(2)
        .collect::<Vec<_>>();
    reversed.extend(
        swapped
            .iter()
            .map(|(from, to)| (from.symbol_id(), to.symbol_id())),
    );
    assert_eq!(
        Renaming::new(source, target, reversed),
        Err(Error::IncidenceChanged {
            column: flow(NEUTRAL.flow).symbol_id(),
            axis: axis(NEUTRAL.left_axis),
        })
    );

    let one_kind = stocks(&[("a", FixtureKind::Q1), ("b", FixtureKind::Q1)]);
    let two_kinds = stocks(&[("x", FixtureKind::Q1), ("y", FixtureKind::Q2)]);
    assert_eq!(
        Renaming::new(
            one_kind,
            two_kinds.clone(),
            [
                (axis("a").symbol_id(), axis("x").symbol_id()),
                (axis("b").symbol_id(), axis("y").symbol_id()),
            ],
        ),
        Err(Error::KindConflict(KindConflict {
            symbol: axis("b").symbol_id(),
            kind: FixtureKind::Q1,
            first: FixtureKind::Q1,
            second: FixtureKind::Q2,
        }))
    );

    let merged = stocks(&[("x", FixtureKind::Quantity), ("y", FixtureKind::Quantity)]);
    assert!(
        Renaming::new(
            stocks(&[("a", FixtureKind::Q1), ("b", FixtureKind::Q2)]),
            merged,
            [
                (axis("a").symbol_id(), axis("x").symbol_id()),
                (axis("b").symbol_id(), axis("y").symbol_id()),
            ],
        )
        .is_ok()
    );
}

proptest! {
    #[test]
    fn generated_models_observe_every_category_and_satisfaction_law(
        left_before in -100i64..100,
        right_before in -100i64..100,
        internal in 0i64..20,
        input in 0i64..20,
        output in 0i64..20,
        equation_holds in any::<bool>(),
        ledgers_hold in any::<bool>(),
        family in 0usize..5,
    ) {
        let source = signature(NEUTRAL);
        let middle = signature(ECOLOGY);
        let target = signature(ECONOMY);
        let last = signature(FOURTH);
        let first = renaming(NEUTRAL, source.clone(), ECOLOGY, middle);
        let second = renaming(ECOLOGY, first.target().clone(), ECONOMY, target.clone());
        let third = renaming(ECONOMY, target.clone(), FOURTH, last);
        let ecological_model = model_with_values(
            first.target(),
            ECOLOGY,
            left_before,
            right_before,
            internal,
            input,
            output,
            equation_holds,
            ledgers_hold,
        );
        let economic_model = model_with_values(
            &target,
            ECONOMY,
            left_before,
            right_before,
            internal,
            input,
            output,
            equation_holds,
            ledgers_hold,
        );
        let source_sentences = sentences(&source, NEUTRAL);
        let source_sentence = &source_sentences[family];

        prop_assert!(laws::check_signature_identity(&STOCK_FLOW, &first).unwrap());
        prop_assert!(laws::check_signature_associativity(
            &STOCK_FLOW,
            &first,
            &second,
            &third,
        ).unwrap());
        prop_assert!(laws::check_sentence_identity(
            &STOCK_FLOW,
            &source,
            source_sentence,
        ).unwrap());
        prop_assert!(laws::check_sentence_composition(
            &STOCK_FLOW,
            &first,
            &second,
            source_sentence,
        ).unwrap());
        prop_assert!(laws::check_model_identity(
            &STOCK_FLOW,
            first.target(),
            &ecological_model,
        ).unwrap());
        prop_assert!(laws::check_model_composition(
            &STOCK_FLOW,
            &first,
            &second,
            &economic_model,
        ).unwrap());
        let square = laws::check_satisfaction_square(
            &STOCK_FLOW,
            &first,
            source_sentence,
            &ecological_model,
        ).unwrap();
        prop_assert!(square.holds());
    }

    #[test]
    fn generated_signed_states_and_nonnegative_flows_survive_reduct(
        left_before in -100i64..100,
        right_before in -100i64..100,
        internal in 0i64..20,
        input in 0i64..20,
        output in 0i64..20,
    ) {
        let source = signature(NEUTRAL);
        let morphism = renaming(NEUTRAL, source.clone(), ECOLOGY, signature(ECOLOGY));
        let target_model = model_with_values(
            morphism.target(),
            ECOLOGY,
            left_before,
            right_before,
            internal,
            input,
            output,
            true,
            true,
        );
        let source_transition = StockFlowSentence::Transition(
            TransitionEquation::new(sentence("generated-transition")),
        );
        let square = laws::check_satisfaction_square(
            &STOCK_FLOW,
            &morphism,
            &source_transition,
            &target_model,
        ).unwrap();
        prop_assert!(square.holds());
        prop_assert!(square.translated_sentence_satisfied());

        let reduced = STOCK_FLOW.reduct(&morphism, &target_model).unwrap();
        prop_assert_eq!(
            reduced.trace().records()[0].before().amount(&axis(NEUTRAL.left_axis)),
            Some(&q(left_before)),
        );
    }
}
