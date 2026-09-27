//! The comorphism from conservation into stock-flow.

mod support;

use conservation_core::{BalanceLaw, Grade, GradedLaw, Provenance};
use conservation_stock_flow::{
    GradedStateLaw, TransitionRecord, TransitionRecordData, TransitionTrace,
};
use institution::{Comorphism, Institution, Renaming, laws};
use institution_conservation::stock_flow::{
    StockFlowInstitution, StockFlowModel, StockFlowSentence, StockFlowSignature,
};
use institution_conservation::{
    ConservationInstitution, ConservationSignature, Error, IntoStockFlow, TraceModel,
};
use support::*;

fn comorphism() -> IntoStockFlow<FixtureKind> {
    IntoStockFlow::new(sentence("conservation"))
}

fn pools() -> ConservationSignature<FixtureKind> {
    ConservationSignature::new([
        (axis("left"), FixtureKind::Quantity),
        (axis("right"), FixtureKind::Quantity),
    ])
    .unwrap()
}

fn law(coefficients: &[(&str, i64)], grade: Grade) -> GradedLaw<FixtureKind> {
    GradedLaw::new(
        BalanceLaw::new(
            FixtureKind::Quantity,
            coefficients
                .iter()
                .map(|(name, value)| (axis(name), q(*value))),
            Provenance::Declared,
        )
        .unwrap(),
        grade,
    )
}

fn total() -> GradedLaw<FixtureKind> {
    law(&[("left", 1), ("right", 1)], Grade::Invariant)
}

fn left_grows() -> GradedLaw<FixtureKind> {
    law(&[("left", 1)], Grade::Nondecreasing)
}

/// A stock-flow model over the image of `signature` whose stock `left` takes
/// the values `lefts` and `right` keeps the total at 6.
fn trace(
    signature: &StockFlowSignature<FixtureKind>,
    lefts: &[i64],
) -> StockFlowModel<FixtureKind> {
    let stocks = |left: i64| {
        amounts([
            (axis("left"), FixtureKind::Quantity, q(left)),
            (axis("right"), FixtureKind::Quantity, q(6 - left)),
        ])
    };
    let records = lefts
        .windows(2)
        .map(|pair| {
            TransitionRecord::new(
                signature.carrier(),
                TransitionRecordData {
                    before: stocks(pair[0]),
                    after: stocks(pair[1]),
                    requested_internal: amounts([]),
                    settled_internal: amounts([]),
                    requested_boundary: amounts([]),
                    settled_boundary: amounts([]),
                    ledger_before: amounts([]),
                    ledger_after: amounts([]),
                },
            )
            .unwrap()
        })
        .collect();
    let trace = TransitionTrace::new(signature.carrier().clone(), records).unwrap();
    StockFlowModel::new(signature.clone(), trace).unwrap()
}

#[test]
fn the_comorphism_square_holds_with_both_truth_values() {
    let comorphism = comorphism();
    let signature = pools();
    let image = comorphism.map_signature(&signature).unwrap();
    let rising = trace(&image, &[1, 2, 3]);
    let falling = trace(&image, &[3, 2, 1]);

    assert_eq!(
        comorphism.translate_sentence(&signature, &left_grows()),
        Ok(StockFlowSentence::Graded(GradedStateLaw::new(
            sentence("conservation"),
            left_grows(),
        )))
    );
    assert_eq!(
        comorphism
            .reduct(&signature, &rising)
            .unwrap()
            .states()
            .len(),
        3
    );

    for (law, model, satisfied) in [
        (total(), &rising, true),
        (total(), &falling, true),
        (left_grows(), &rising, true),
        (left_grows(), &falling, false),
    ] {
        let square =
            laws::check_comorphism_satisfaction(&comorphism, &signature, &law, model).unwrap();
        assert!(square.holds());
        assert_eq!(square.translated_sentence_satisfied(), satisfied);
    }
    let grows = left_grows();
    assert!(
        laws::check_comorphism_non_vacuity(
            &comorphism,
            [&rising, &falling]
                .into_iter()
                .map(|model| (&signature, &grows, model)),
        )
        .is_ok_and(|evidence| evidence.is_non_vacuous())
    );
}

/// The comorphism, except that its reduct reads the trace backwards.
struct ReadsBackwards(IntoStockFlow<FixtureKind>);

impl Comorphism for ReadsBackwards {
    type Source = ConservationInstitution<FixtureKind>;
    type Target = StockFlowInstitution<FixtureKind>;
    type Error = Error<FixtureKind>;

    fn source_institution(&self) -> &Self::Source {
        self.0.source_institution()
    }

    fn target_institution(&self) -> &Self::Target {
        self.0.target_institution()
    }

    fn map_signature(
        &self,
        signature: &ConservationSignature<FixtureKind>,
    ) -> Result<StockFlowSignature<FixtureKind>, Self::Error> {
        self.0.map_signature(signature)
    }

    fn map_signature_morphism(
        &self,
        morphism: &Renaming<ConservationSignature<FixtureKind>>,
    ) -> Result<Renaming<StockFlowSignature<FixtureKind>>, Self::Error> {
        self.0.map_signature_morphism(morphism)
    }

    fn translate_sentence(
        &self,
        signature: &ConservationSignature<FixtureKind>,
        sentence: &GradedLaw<FixtureKind>,
    ) -> Result<StockFlowSentence<FixtureKind>, Self::Error> {
        self.0.translate_sentence(signature, sentence)
    }

    fn reduct(
        &self,
        signature: &ConservationSignature<FixtureKind>,
        model: &StockFlowModel<FixtureKind>,
    ) -> Result<TraceModel<FixtureKind>, Self::Error> {
        let reduced = self.0.reduct(signature, model)?;
        TraceModel::new(
            signature.clone(),
            reduced.states().iter().rev().cloned().collect(),
        )
    }
}

#[test]
fn a_reduct_that_reads_the_trace_backwards_breaks_the_comorphism_square() {
    let signature = pools();
    let rising = trace(&comorphism().map_signature(&signature).unwrap(), &[1, 2, 3]);
    let square = laws::check_comorphism_satisfaction(
        &ReadsBackwards(comorphism()),
        &signature,
        &left_grows(),
        &rising,
    )
    .unwrap();
    assert!(!square.holds());
    assert!(square.translated_sentence_satisfied());
    assert!(!square.reduced_model_satisfies_source_sentence());
}

#[test]
fn a_renaming_that_forgets_axes_is_refused_by_name() {
    let three = ConservationSignature::new([
        (axis("x"), FixtureKind::Mass),
        (axis("y"), FixtureKind::Mass),
        (axis("z"), FixtureKind::Mass),
    ])
    .unwrap();
    let forgetting = Renaming::new(
        pools(),
        three,
        [(axis("left"), axis("x")), (axis("right"), axis("y"))],
    )
    .unwrap();
    assert_eq!(
        comorphism().map_signature_morphism(&forgetting),
        Err(Error::ForgetsAxes(vec![axis("z")]))
    );
}

#[test]
fn an_axis_bijective_renaming_commutes_through_the_comorphism() {
    let comorphism = comorphism();
    let target = ConservationSignature::new([
        (axis("x"), FixtureKind::Mass),
        (axis("y"), FixtureKind::Mass),
    ])
    .unwrap();
    let renaming = Renaming::new(
        pools(),
        target.clone(),
        [(axis("left"), axis("y")), (axis("right"), axis("x"))],
    )
    .unwrap();
    let mapped = comorphism.map_signature_morphism(&renaming).unwrap();
    assert_eq!(
        mapped.source(),
        &comorphism.map_signature(&pools()).unwrap()
    );
    assert_eq!(mapped.target(), &comorphism.map_signature(&target).unwrap());

    let stock_flow = StockFlowInstitution::<FixtureKind>::new();
    let conservation = ConservationInstitution::<FixtureKind>::new();
    for law in [total(), left_grows()] {
        // Translate then embed equals embed then translate.
        assert_eq!(
            comorphism
                .translate_sentence(
                    &target,
                    &conservation.translate_sentence(&renaming, &law).unwrap(),
                )
                .unwrap(),
            stock_flow
                .translate_sentence(
                    &mapped,
                    &comorphism.translate_sentence(&pools(), &law).unwrap(),
                )
                .unwrap()
        );
    }

    // Reduce then reduce equals reduce then reduce.
    let model = StockFlowModel::new(
        mapped.target().clone(),
        TransitionTrace::new(
            mapped.target().carrier().clone(),
            vec![
                TransitionRecord::new(
                    mapped.target().carrier(),
                    TransitionRecordData {
                        before: amounts([
                            (axis("x"), FixtureKind::Mass, q(1)),
                            (axis("y"), FixtureKind::Mass, q(5)),
                        ]),
                        after: amounts([
                            (axis("x"), FixtureKind::Mass, q(2)),
                            (axis("y"), FixtureKind::Mass, q(4)),
                        ]),
                        requested_internal: amounts([]),
                        settled_internal: amounts([]),
                        requested_boundary: amounts([]),
                        settled_boundary: amounts([]),
                        ledger_before: amounts([]),
                        ledger_after: amounts([]),
                    },
                )
                .unwrap(),
            ],
        )
        .unwrap(),
    )
    .unwrap();
    assert_eq!(
        conservation
            .reduct(&renaming, &comorphism.reduct(&target, &model).unwrap())
            .unwrap(),
        comorphism
            .reduct(&pools(), &stock_flow.reduct(&mapped, &model).unwrap())
            .unwrap()
    );
}
