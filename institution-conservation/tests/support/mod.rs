#![allow(dead_code)]

use std::sync::Arc;

use conservation_core::{AxisId, BalanceLaw, Grade, GradedLaw, Provenance};
use conservation_dynamics::{FlowSpec, FlowTopology, ProcessId, StockDefinition, StockId};
use conservation_stock_flow::{
    BoundaryCorrespondence, BoundaryId, ChannelId, ExactAmounts, FlowId, GradedStateLaw,
    LedgerDefinition, LedgerId, LinearFlowConstraint, SentenceId, StockAxisDefinition,
    StockFlowCarrier, Symbol, SymbolId, TransitionEquation, TransitionRecord, TransitionRecordData,
    TransitionTrace, certify_nullspace,
};
use institution::Renaming;
use institution_conservation::ConservationInstitution;
use institution_conservation::stock_flow::{
    StockFlowInstitution, StockFlowModel, StockFlowSentence, StockFlowSignature,
};
use num_bigint::BigInt;
use num_rational::BigRational;

pub mod kinds;

pub use kinds::FixtureKind;

pub const CONSERVATION: ConservationInstitution<FixtureKind> = ConservationInstitution::new();
pub const STOCK_FLOW: StockFlowInstitution<FixtureKind> = StockFlowInstitution::new();

#[derive(Clone, Copy)]
pub struct Names {
    pub kind: FixtureKind,
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
    kind: FixtureKind::Quantity,
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
    kind: FixtureKind::Biomass,
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
    kind: FixtureKind::Money,
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
    kind: FixtureKind::Energy,
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
    values: impl IntoIterator<Item = (I, FixtureKind, BigRational)>,
) -> ExactAmounts<I, FixtureKind> {
    ExactAmounts::new(values).unwrap()
}

pub fn signature(names: Names) -> StockFlowSignature<FixtureKind> {
    signature_with(names, true)
}

/// The two-stock carrier of `names`, with its output ledger only when
/// `output_ledger` is set.
pub fn signature_with(names: Names, output_ledger: bool) -> StockFlowSignature<FixtureKind> {
    let quantity = names.kind;
    let mut ledgers = vec![LedgerDefinition {
        id: ledger(names.input_ledger),
        axis: axis(names.input_ledger_axis),
        kind: quantity,
        boundaries: vec![boundary(names.input)],
    }];
    if output_ledger {
        ledgers.push(LedgerDefinition {
            id: ledger(names.output_ledger),
            axis: axis(names.output_ledger_axis),
            kind: quantity,
            boundaries: vec![boundary(names.output)],
        });
    }
    let left = StockId::new(names.left_stock).unwrap();
    let right = StockId::new(names.right_stock).unwrap();
    let topology = FlowTopology::new(
        [
            StockDefinition {
                id: left.clone(),
                kind: quantity,
            },
            StockDefinition {
                id: right.clone(),
                kind: quantity,
            },
        ],
        [
            FlowSpec {
                process: ProcessId::new("internal-process").unwrap(),
                kind: quantity,
                source: Some(left.clone()),
                target: Some(right.clone()),
            },
            FlowSpec {
                process: ProcessId::new("input-process").unwrap(),
                kind: quantity,
                source: None,
                target: Some(left.clone()),
            },
            FlowSpec {
                process: ProcessId::new("output-process").unwrap(),
                kind: quantity,
                source: Some(right.clone()),
                target: None,
            },
        ],
        [],
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
        ledgers,
    )
    .unwrap();
    StockFlowSignature::new(Arc::new(carrier))
}

/// Every symbol of the input-ledger-only carrier of `source_names`, paired
/// with its namesake in `target_names`.
pub fn shared_pairs(source_names: Names, target_names: Names) -> Vec<(SymbolId, SymbolId)> {
    vec![
        (
            axis(source_names.left_axis).symbol_id(),
            axis(target_names.left_axis).symbol_id(),
        ),
        (
            axis(source_names.right_axis).symbol_id(),
            axis(target_names.right_axis).symbol_id(),
        ),
        (
            axis(source_names.input_ledger_axis).symbol_id(),
            axis(target_names.input_ledger_axis).symbol_id(),
        ),
        (
            flow(source_names.flow).symbol_id(),
            flow(target_names.flow).symbol_id(),
        ),
        (
            boundary(source_names.input).symbol_id(),
            boundary(target_names.input).symbol_id(),
        ),
        (
            boundary(source_names.output).symbol_id(),
            boundary(target_names.output).symbol_id(),
        ),
        (
            ledger(source_names.input_ledger).symbol_id(),
            ledger(target_names.input_ledger).symbol_id(),
        ),
    ]
}

/// The renaming from the input-ledger-only carrier of `source_names` into the
/// full carrier of `target_names`. It forgets the output ledger and its axis.
pub fn forgetting_renaming(
    source_names: Names,
    target_names: Names,
) -> Renaming<StockFlowSignature<FixtureKind>> {
    Renaming::new(
        signature_with(source_names, false),
        signature(target_names),
        shared_pairs(source_names, target_names),
    )
    .unwrap()
}

pub fn renaming(
    source_names: Names,
    source: StockFlowSignature<FixtureKind>,
    target_names: Names,
    target: StockFlowSignature<FixtureKind>,
) -> Renaming<StockFlowSignature<FixtureKind>> {
    let mut pairs = shared_pairs(source_names, target_names);
    pairs.push((
        axis(source_names.output_ledger_axis).symbol_id(),
        axis(target_names.output_ledger_axis).symbol_id(),
    ));
    pairs.push((
        ledger(source_names.output_ledger).symbol_id(),
        ledger(target_names.output_ledger).symbol_id(),
    ));
    Renaming::new(source, target, pairs).unwrap()
}

#[allow(clippy::too_many_arguments)]
pub fn model_with_values(
    signature: &StockFlowSignature<FixtureKind>,
    names: Names,
    left_before: i64,
    right_before: i64,
    internal: i64,
    input: i64,
    output: i64,
    equation_holds: bool,
    ledgers_hold: bool,
) -> StockFlowModel<FixtureKind> {
    let quantity = names.kind;
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
                (axis(names.left_axis), quantity, q(left_before)),
                (axis(names.right_axis), quantity, q(right_before)),
            ]),
            after: amounts([
                (axis(names.left_axis), quantity, q(left_after)),
                (axis(names.right_axis), quantity, q(right_after)),
            ]),
            requested_internal: amounts([(flow(names.flow), quantity, q(internal))]),
            settled_internal: amounts([(flow(names.flow), quantity, q(internal))]),
            requested_boundary: amounts([
                (boundary(names.input), quantity, q(input)),
                (boundary(names.output), quantity, q(output)),
            ]),
            settled_boundary: amounts([
                (boundary(names.input), quantity, q(input)),
                (boundary(names.output), quantity, q(output)),
            ]),
            ledger_before: amounts([
                (ledger(names.input_ledger), quantity, q(10)),
                (ledger(names.output_ledger), quantity, q(-5)),
            ]),
            ledger_after: amounts([
                (ledger(names.input_ledger), quantity, q(input_after)),
                (ledger(names.output_ledger), quantity, q(-5 + output)),
            ]),
        },
    )
    .unwrap();
    let trace = TransitionTrace::new(signature.carrier().clone(), vec![record]).unwrap();
    StockFlowModel::new(signature.clone(), trace).unwrap()
}

/// `model` with its output ledger moved by `drift` more than its ports explain.
pub fn with_output_ledger_drift(
    model: &StockFlowModel<FixtureKind>,
    names: Names,
    drift: i64,
) -> StockFlowModel<FixtureKind> {
    let signature = model.signature();
    let mut data = model.trace().records()[0].clone().into_data();
    let ledger_after = data
        .ledger_after
        .iter()
        .map(|(id, kind, amount)| {
            let amount = if id == &ledger(names.output_ledger) {
                amount + q(drift)
            } else {
                amount.clone()
            };
            (id.clone(), kind, amount)
        })
        .collect::<Vec<_>>();
    data.ledger_after = amounts(ledger_after);
    let record = TransitionRecord::new(signature.carrier(), data).unwrap();
    let trace = TransitionTrace::new(signature.carrier().clone(), vec![record]).unwrap();
    StockFlowModel::new(signature.clone(), trace).unwrap()
}

pub fn valid_model(
    signature: &StockFlowSignature<FixtureKind>,
    names: Names,
) -> StockFlowModel<FixtureKind> {
    model_with_values(signature, names, -2, 12, 3, 2, 1, true, true)
}

pub fn sentences(
    signature: &StockFlowSignature<FixtureKind>,
    names: Names,
) -> Vec<StockFlowSentence<FixtureKind>> {
    let quantity = names.kind;
    let graded = GradedLaw::new(
        BalanceLaw::new(
            quantity,
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
        quantity,
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
