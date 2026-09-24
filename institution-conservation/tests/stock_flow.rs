mod support;

use conservation_core::{BalanceLaw, Grade, GradedLaw, Provenance};
use conservation_stock_flow::{
    GradedStateLaw, LinearFlowConstraint, StockFlowError, SymbolId, TransitionEquation,
    TransitionRecord, certify_nullspace,
};
use institution::{Institution, laws};
use institution_conservation::stock_flow::{
    Error, StockFlowInstitution, StockFlowRenaming, StockFlowSentence,
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
            kind(NEUTRAL.kind),
            [(flow(NEUTRAL.flow), q(1))],
            q(4),
        )
        .unwrap(),
    );
    let false_graded = StockFlowSentence::Graded(GradedStateLaw::new(
        sentence("false-graded"),
        GradedLaw::new(
            BalanceLaw::new(
                kind(NEUTRAL.kind),
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
    assert!(matches!(
        StockFlowRenaming::new(
            source.clone(),
            target.clone(),
            [(kind(NEUTRAL.kind), kind(ECOLOGY.kind))],
            [
                (axis(NEUTRAL.left_axis), axis(ECOLOGY.left_axis)),
                (axis(NEUTRAL.right_axis), axis(ECOLOGY.right_axis)),
            ],
            [(flow(NEUTRAL.flow), flow(ECOLOGY.flow))],
            [
                (boundary(NEUTRAL.input), boundary(ECOLOGY.input)),
                (boundary(NEUTRAL.output), boundary(ECOLOGY.output)),
            ],
            [
                (ledger(NEUTRAL.input_ledger), ledger(ECOLOGY.input_ledger)),
                (ledger(NEUTRAL.output_ledger), ledger(ECOLOGY.output_ledger)),
            ],
        ),
        Err(Error::InvalidMorphism(_))
    ));
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
                kind(NEUTRAL.kind),
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
        kind(ECONOMY.kind),
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
    data.requested_internal = amounts([(flow(NEUTRAL.flow), kind(NEUTRAL.kind), q(-1))]);
    assert_eq!(
        TransitionRecord::new(signature.carrier(), data),
        Err(StockFlowError::NegativeAmount(SymbolId::Flow(flow(
            NEUTRAL.flow
        ))))
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
