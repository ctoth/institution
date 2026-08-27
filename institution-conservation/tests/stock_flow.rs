use std::sync::Arc;

use conservation_core::{AxisId, BalanceLaw, Grade, GradedLaw, KindId, Provenance};
use conservation_dynamics::{FlowSpec, FlowTopology, ProcessId, StockDefinition, StockId};
use conservation_stock_flow::{
    BoundaryCorrespondence, BoundaryId, ChannelId, ExactAmounts, FlowId, GradedStateLaw,
    LedgerDefinition, LedgerId, LinearFlowConstraint, SentenceId, StockAxisDefinition,
    StockFlowCarrier, StockFlowError, Symbol, SymbolId, TransitionEquation, TransitionRecord,
    TransitionRecordData, TransitionTrace, certify_nullspace,
};
use institution::{Institution, laws};
use institution_conservation::stock_flow::{
    Error, StockFlowInstitution, StockFlowModel, StockFlowRenaming, StockFlowSentence,
    StockFlowSignature,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use proptest::prelude::*;

#[derive(Clone, Copy)]
struct Names {
    kind: &'static str,
    left_stock: &'static str,
    right_stock: &'static str,
    left_axis: &'static str,
    right_axis: &'static str,
    flow: &'static str,
    input: &'static str,
    output: &'static str,
    input_ledger: &'static str,
    output_ledger: &'static str,
    input_ledger_axis: &'static str,
    output_ledger_axis: &'static str,
}

const NEUTRAL: Names = Names {
    kind: "quantity",
    left_stock: "left-stock",
    right_stock: "right-stock",
    left_axis: "left",
    right_axis: "right",
    flow: "transfer",
    input: "input",
    output: "output",
    input_ledger: "inputs-ledger",
    output_ledger: "outputs-ledger",
    input_ledger_axis: "inputs-cumulative",
    output_ledger_axis: "outputs-cumulative",
};

const ECOLOGY: Names = Names {
    kind: "biomass",
    left_stock: "producer-stock",
    right_stock: "consumer-stock",
    left_axis: "producer-pool",
    right_axis: "consumer-pool",
    flow: "feeding",
    input: "primary-production",
    output: "respiration",
    input_ledger: "production-ledger",
    output_ledger: "respiration-ledger",
    input_ledger_axis: "produced-cumulative",
    output_ledger_axis: "respired-cumulative",
};

const ECONOMY: Names = Names {
    kind: "money",
    left_stock: "deposit-stock",
    right_stock: "cash-stock",
    left_axis: "deposits",
    right_axis: "cash",
    flow: "payment",
    input: "income",
    output: "expenditure",
    input_ledger: "income-ledger",
    output_ledger: "expenditure-ledger",
    input_ledger_axis: "income-cumulative",
    output_ledger_axis: "expenditure-cumulative",
};

const FOURTH: Names = Names {
    kind: "energy",
    left_stock: "upper-stock",
    right_stock: "lower-stock",
    left_axis: "upper",
    right_axis: "lower",
    flow: "conversion",
    input: "forcing",
    output: "dissipation",
    input_ledger: "forcing-ledger",
    output_ledger: "dissipation-ledger",
    input_ledger_axis: "forced-cumulative",
    output_ledger_axis: "dissipated-cumulative",
};

fn q(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn axis(value: &str) -> AxisId {
    AxisId::new(value).unwrap()
}

fn kind(value: &str) -> KindId {
    KindId::new(value).unwrap()
}

fn flow(value: &str) -> FlowId {
    FlowId::new(value).unwrap()
}

fn boundary(value: &str) -> BoundaryId {
    BoundaryId::new(value).unwrap()
}

fn ledger(value: &str) -> LedgerId {
    LedgerId::new(value).unwrap()
}

fn sentence(value: &str) -> SentenceId {
    SentenceId::new(value).unwrap()
}

fn amounts<I: Symbol>(
    values: impl IntoIterator<Item = (I, KindId, BigRational)>,
) -> ExactAmounts<I> {
    ExactAmounts::new(values).unwrap()
}

fn signature(names: Names) -> StockFlowSignature {
    let quantity = kind(names.kind);
    let left = StockId::new(names.left_stock).unwrap();
    let right = StockId::new(names.right_stock).unwrap();
    let topology = FlowTopology::new(
        [
            StockDefinition {
                id: left.clone(),
                kind: quantity.clone(),
            },
            StockDefinition {
                id: right.clone(),
                kind: quantity.clone(),
            },
        ],
        [
            FlowSpec {
                process: ProcessId::new("internal-process").unwrap(),
                kind: quantity.clone(),
                source: Some(left.clone()),
                target: Some(right.clone()),
            },
            FlowSpec {
                process: ProcessId::new("input-process").unwrap(),
                kind: quantity.clone(),
                source: None,
                target: Some(left.clone()),
            },
            FlowSpec {
                process: ProcessId::new("output-process").unwrap(),
                kind: quantity.clone(),
                source: Some(right.clone()),
                target: None,
            },
        ],
    )
    .unwrap();
    let carrier = StockFlowCarrier::new(
        Arc::new(topology),
        [
            StockAxisDefinition {
                stock: left,
                axis: axis(names.left_axis),
            },
            StockAxisDefinition {
                stock: right,
                axis: axis(names.right_axis),
            },
        ],
        [
            ChannelId::Internal(flow(names.flow)),
            ChannelId::Boundary(boundary(names.input)),
            ChannelId::Boundary(boundary(names.output)),
        ],
        [
            LedgerDefinition {
                id: ledger(names.input_ledger),
                axis: axis(names.input_ledger_axis),
                kind: quantity.clone(),
                boundaries: vec![boundary(names.input)],
            },
            LedgerDefinition {
                id: ledger(names.output_ledger),
                axis: axis(names.output_ledger_axis),
                kind: quantity,
                boundaries: vec![boundary(names.output)],
            },
        ],
    )
    .unwrap();
    StockFlowSignature::new(Arc::new(carrier))
}

fn renaming(
    source_names: Names,
    source: StockFlowSignature,
    target_names: Names,
    target: StockFlowSignature,
) -> StockFlowRenaming {
    StockFlowRenaming::new(
        source,
        target,
        [(kind(source_names.kind), kind(target_names.kind))],
        [
            (axis(source_names.left_axis), axis(target_names.left_axis)),
            (axis(source_names.right_axis), axis(target_names.right_axis)),
            (
                axis(source_names.input_ledger_axis),
                axis(target_names.input_ledger_axis),
            ),
            (
                axis(source_names.output_ledger_axis),
                axis(target_names.output_ledger_axis),
            ),
        ],
        [(flow(source_names.flow), flow(target_names.flow))],
        [
            (boundary(source_names.input), boundary(target_names.input)),
            (boundary(source_names.output), boundary(target_names.output)),
        ],
        [
            (
                ledger(source_names.input_ledger),
                ledger(target_names.input_ledger),
            ),
            (
                ledger(source_names.output_ledger),
                ledger(target_names.output_ledger),
            ),
        ],
    )
    .unwrap()
}

#[allow(clippy::too_many_arguments)]
fn model_with_values(
    signature: &StockFlowSignature,
    names: Names,
    left_before: i64,
    right_before: i64,
    internal: i64,
    input: i64,
    output: i64,
    equation_holds: bool,
    ledgers_hold: bool,
) -> StockFlowModel {
    let quantity = kind(names.kind);
    let left_after = if equation_holds {
        left_before - internal + input
    } else {
        left_before
    };
    let right_after = if equation_holds {
        right_before + internal - output
    } else {
        right_before
    };
    let input_after = if ledgers_hold { 10 + input } else { 9 + input };
    let record = TransitionRecord::new(
        signature.carrier(),
        TransitionRecordData {
            before: amounts([
                (axis(names.left_axis), quantity.clone(), q(left_before)),
                (axis(names.right_axis), quantity.clone(), q(right_before)),
            ]),
            after: amounts([
                (axis(names.left_axis), quantity.clone(), q(left_after)),
                (axis(names.right_axis), quantity.clone(), q(right_after)),
            ]),
            requested_internal: amounts([(flow(names.flow), quantity.clone(), q(internal))]),
            settled_internal: amounts([(flow(names.flow), quantity.clone(), q(internal))]),
            requested_boundary: amounts([
                (boundary(names.input), quantity.clone(), q(input)),
                (boundary(names.output), quantity.clone(), q(output)),
            ]),
            settled_boundary: amounts([
                (boundary(names.input), quantity.clone(), q(input)),
                (boundary(names.output), quantity.clone(), q(output)),
            ]),
            ledger_before: amounts([
                (ledger(names.input_ledger), quantity.clone(), q(10)),
                (ledger(names.output_ledger), quantity.clone(), q(-5)),
            ]),
            ledger_after: amounts([
                (ledger(names.input_ledger), quantity.clone(), q(input_after)),
                (ledger(names.output_ledger), quantity, q(-5 + output)),
            ]),
        },
    )
    .unwrap();
    let trace = TransitionTrace::new(signature.carrier().clone(), vec![record]).unwrap();
    StockFlowModel::new(signature.clone(), trace).unwrap()
}

fn valid_model(signature: &StockFlowSignature, names: Names) -> StockFlowModel {
    model_with_values(signature, names, -2, 12, 3, 2, 1, true, true)
}

fn sentences(signature: &StockFlowSignature, names: Names) -> Vec<StockFlowSentence> {
    let quantity = kind(names.kind);
    let graded = GradedLaw::new(
        BalanceLaw::new(
            quantity.clone(),
            [
                (axis(names.left_axis), q(1)),
                (axis(names.right_axis), q(1)),
                (axis(names.input_ledger_axis), q(-1)),
                (axis(names.output_ledger_axis), q(1)),
            ],
            Provenance::Declared,
        )
        .unwrap(),
        Grade::Invariant,
    );
    let certificate = certify_nullspace(
        signature.carrier(),
        quantity.clone(),
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
                quantity,
                [(flow(names.flow), q(1))],
                q(3),
            )
            .unwrap(),
        ),
        StockFlowSentence::Boundary(BoundaryCorrespondence::new(
            sentence("boundary"),
            ledger(names.input_ledger),
        )),
        StockFlowSentence::Graded(GradedStateLaw::new(sentence("graded"), graded)),
        StockFlowSentence::OpenBalance(certificate.open_balance(sentence("open-balance"))),
    ]
}

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
    let institution = StockFlowInstitution;

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
        let square = laws::check_satisfaction_square(
            &StockFlowInstitution,
            &morphism,
            sentence,
            target_model,
        )
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
                laws::check_satisfaction_square(&StockFlowInstitution, morphism, &sentence, &model)
                    .unwrap();
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
        StockFlowInstitution.satisfies(&source, &target_model, &sentences(&source, NEUTRAL)[0]),
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
        StockFlowInstitution.translate_sentence(&valid_renaming, &outside),
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
        StockFlowInstitution.translate_sentence(&valid_renaming, &foreign),
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

        prop_assert!(laws::check_signature_identity(&StockFlowInstitution, &first).unwrap());
        prop_assert!(laws::check_signature_associativity(
            &StockFlowInstitution,
            &first,
            &second,
            &third,
        ).unwrap());
        prop_assert!(laws::check_sentence_identity(
            &StockFlowInstitution,
            &source,
            source_sentence,
        ).unwrap());
        prop_assert!(laws::check_sentence_composition(
            &StockFlowInstitution,
            &first,
            &second,
            source_sentence,
        ).unwrap());
        prop_assert!(laws::check_model_identity(
            &StockFlowInstitution,
            first.target(),
            &ecological_model,
        ).unwrap());
        prop_assert!(laws::check_model_composition(
            &StockFlowInstitution,
            &first,
            &second,
            &economic_model,
        ).unwrap());
        let square = laws::check_satisfaction_square(
            &StockFlowInstitution,
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
            &StockFlowInstitution,
            &morphism,
            &source_transition,
            &target_model,
        ).unwrap();
        prop_assert!(square.holds());
        prop_assert!(square.translated_sentence_satisfied());

        let reduced = StockFlowInstitution.reduct(&morphism, &target_model).unwrap();
        prop_assert_eq!(
            reduced.trace().records()[0].before().amount(&axis(NEUTRAL.left_axis)),
            Some(&q(left_before)),
        );
    }
}
