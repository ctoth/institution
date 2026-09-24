#![allow(dead_code)]

use std::sync::Arc;

use conservation_core::{AxisId, BalanceLaw, Grade, GradedLaw, KindId, Provenance};
use conservation_dynamics::{FlowSpec, FlowTopology, ProcessId, StockDefinition, StockId};
use conservation_stock_flow::{
    BoundaryCorrespondence, BoundaryId, ChannelId, ExactAmounts, FlowId, GradedStateLaw,
    LedgerDefinition, LedgerId, LinearFlowConstraint, SentenceId, StockAxisDefinition,
    StockFlowCarrier, Symbol, TransitionEquation, TransitionRecord, TransitionRecordData,
    TransitionTrace, certify_nullspace,
};
use institution_conservation::stock_flow::{
    StockFlowModel, StockFlowRenaming, StockFlowSentence, StockFlowSignature,
};
use num_bigint::BigInt;
use num_rational::BigRational;

#[derive(Clone, Copy)]
pub struct Names {
    pub kind: &'static str,
    pub left_stock: &'static str,
    pub right_stock: &'static str,
    pub left_axis: &'static str,
    pub right_axis: &'static str,
    pub flow: &'static str,
    pub input: &'static str,
    pub output: &'static str,
    pub input_ledger: &'static str,
    pub output_ledger: &'static str,
    pub input_ledger_axis: &'static str,
    pub output_ledger_axis: &'static str,
}

pub const NEUTRAL: Names = Names {
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

pub const ECOLOGY: Names = Names {
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

pub const ECONOMY: Names = Names {
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

pub const FOURTH: Names = Names {
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

pub fn q(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

pub fn axis(value: &str) -> AxisId {
    AxisId::new(value).unwrap()
}

pub fn kind(value: &str) -> KindId {
    KindId::new(value).unwrap()
}

pub fn flow(value: &str) -> FlowId {
    FlowId::new(value).unwrap()
}

pub fn boundary(value: &str) -> BoundaryId {
    BoundaryId::new(value).unwrap()
}

pub fn ledger(value: &str) -> LedgerId {
    LedgerId::new(value).unwrap()
}

pub fn sentence(value: &str) -> SentenceId {
    SentenceId::new(value).unwrap()
}

pub fn amounts<I: Symbol>(
    values: impl IntoIterator<Item = (I, KindId, BigRational)>,
) -> ExactAmounts<I> {
    ExactAmounts::new(values).unwrap()
}

pub fn signature(names: Names) -> StockFlowSignature {
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

pub fn renaming(
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
pub fn model_with_values(
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

pub fn valid_model(signature: &StockFlowSignature, names: Names) -> StockFlowModel {
    model_with_values(signature, names, -2, 12, 3, 2, 1, true, true)
}

pub fn sentences(signature: &StockFlowSignature, names: Names) -> Vec<StockFlowSentence> {
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
