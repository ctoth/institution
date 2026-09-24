mod support;

use std::collections::{BTreeMap, BTreeSet};

use conservation_stock_flow::{FlowId, TransitionEquation};
use institution::comorphism::ComorphismError;
use institution::join::{
    Bridge, Join, JoinError, JoinedModel, JoinedSentence, JoinedSignature, JoinedSignatureMorphism,
    Pair,
};
use institution::{Comorphism, Institution, laws};
use institution_conservation::stock_flow::{
    Error, StockFlowInstitution, StockFlowModel, StockFlowRenaming, StockFlowSentence,
    StockFlowSignature,
};
use num_rational::BigRational;
use support::*;

#[derive(Clone, Debug, Eq, PartialEq)]
struct Vocabulary(BTreeSet<String>);

impl Vocabulary {
    fn new(names: &[&str]) -> Self {
        Self(names.iter().map(|name| String::from(*name)).collect())
    }
}

/// Total map of variables into the target; may be non-injective and non-surjective.
#[derive(Clone, Debug, Eq, PartialEq)]
struct VariableMap {
    source: Vocabulary,
    target: Vocabulary,
    map: BTreeMap<String, String>,
}

/// `product = left * right`, exactly.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Product {
    product: String,
    left: String,
    right: String,
}

impl Product {
    fn new(product: &str, left: &str, right: &str) -> Self {
        Self {
            product: product.into(),
            left: left.into(),
            right: right.into(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Values {
    vocabulary: Vocabulary,
    values: BTreeMap<String, BigRational>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ProductError {
    MapNotTotal,
    ImageOutsideTarget(String),
    NotComposable,
    UnknownVariable(String),
    VocabularyMismatch,
    MissingValue(String),
    OutsideComorphismDomain,
}

/// A toy constitutive institution of exact product equations.
struct Products;

impl Products {
    fn validate(map: &VariableMap) -> Result<(), ProductError> {
        if !map.map.keys().eq(map.source.0.iter()) {
            return Err(ProductError::MapNotTotal);
        }
        if let Some(image) = map
            .map
            .values()
            .find(|image| !map.target.0.contains(*image))
        {
            return Err(ProductError::ImageOutsideTarget(image.clone()));
        }
        Ok(())
    }

    fn rename(map: &VariableMap, name: &str) -> Result<String, ProductError> {
        map.map
            .get(name)
            .cloned()
            .ok_or_else(|| ProductError::UnknownVariable(name.into()))
    }

    fn value<'a>(
        vocabulary: &Vocabulary,
        model: &'a Values,
        name: &str,
    ) -> Result<&'a BigRational, ProductError> {
        if !vocabulary.0.contains(name) {
            return Err(ProductError::UnknownVariable(name.into()));
        }
        model
            .values
            .get(name)
            .ok_or_else(|| ProductError::MissingValue(name.into()))
    }
}

impl Institution for Products {
    type Signature = Vocabulary;
    type SignatureMorphism = VariableMap;
    type Sentence = Product;
    type Model = Values;
    type Error = ProductError;

    fn source<'a>(&self, morphism: &'a VariableMap) -> &'a Vocabulary {
        &morphism.source
    }

    fn target<'a>(&self, morphism: &'a VariableMap) -> &'a Vocabulary {
        &morphism.target
    }

    fn identity(&self, signature: &Vocabulary) -> Result<VariableMap, ProductError> {
        Ok(VariableMap {
            source: signature.clone(),
            target: signature.clone(),
            map: signature
                .0
                .iter()
                .map(|name| (name.clone(), name.clone()))
                .collect(),
        })
    }

    fn compose(
        &self,
        first: &VariableMap,
        second: &VariableMap,
    ) -> Result<VariableMap, ProductError> {
        Self::validate(first)?;
        Self::validate(second)?;
        if first.target != second.source {
            return Err(ProductError::NotComposable);
        }
        let map = first
            .map
            .iter()
            .map(|(name, middle)| Ok((name.clone(), Self::rename(second, middle)?)))
            .collect::<Result<_, ProductError>>()?;
        Ok(VariableMap {
            source: first.source.clone(),
            target: second.target.clone(),
            map,
        })
    }

    fn translate_sentence(
        &self,
        morphism: &VariableMap,
        sentence: &Product,
    ) -> Result<Product, ProductError> {
        Self::validate(morphism)?;
        Ok(Product {
            product: Self::rename(morphism, &sentence.product)?,
            left: Self::rename(morphism, &sentence.left)?,
            right: Self::rename(morphism, &sentence.right)?,
        })
    }

    fn reduct(&self, morphism: &VariableMap, model: &Values) -> Result<Values, ProductError> {
        Self::validate(morphism)?;
        if model.vocabulary != morphism.target {
            return Err(ProductError::VocabularyMismatch);
        }
        let values = morphism
            .map
            .iter()
            .map(|(name, image)| {
                Ok((
                    name.clone(),
                    Self::value(&morphism.target, model, image)?.clone(),
                ))
            })
            .collect::<Result<_, ProductError>>()?;
        Ok(Values {
            vocabulary: morphism.source.clone(),
            values,
        })
    }

    fn satisfies(
        &self,
        signature: &Vocabulary,
        model: &Values,
        sentence: &Product,
    ) -> Result<bool, ProductError> {
        if &model.vocabulary != signature {
            return Err(ProductError::VocabularyMismatch);
        }
        let product = Self::value(signature, model, &sentence.product)?;
        let left = Self::value(signature, model, &sentence.left)?;
        let right = Self::value(signature, model, &sentence.right)?;
        Ok(*product == left * right)
    }
}

/// In every record, `settled_internal(flow) == left * right`.
#[derive(Clone, Debug, Eq, PartialEq)]
struct SettledProduct {
    flow: FlowId,
    left: String,
    right: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SettlementVerdict {
    Satisfied,
    WrongSettlement {
        record: usize,
        settled: BigRational,
        expected: BigRational,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SettlementError {
    UnknownFlow(FlowId),
    Products(ProductError),
    CarrierMismatch,
}

/// Translates flows through the stock-flow renaming and names through the variable map.
struct SettlementBridge;

/// Returns bridge sentences unchanged, ignoring the variable map.
struct StaleSettlementBridge;

fn evaluate_settlement(
    signature: &Pair<Vocabulary, StockFlowSignature<FixtureKind>>,
    model: &Pair<Values, StockFlowModel<FixtureKind>>,
    sentence: &SettledProduct,
) -> Result<SettlementVerdict, SettlementError> {
    if model.left.vocabulary != signature.left {
        return Err(SettlementError::Products(ProductError::VocabularyMismatch));
    }
    if model.right.signature() != &signature.right {
        return Err(SettlementError::CarrierMismatch);
    }
    let left = Products::value(&signature.left, &model.left, &sentence.left)
        .map_err(SettlementError::Products)?;
    let right = Products::value(&signature.left, &model.left, &sentence.right)
        .map_err(SettlementError::Products)?;
    let expected = left * right;
    for (record, transition) in model.right.trace().records().iter().enumerate() {
        let settled = transition
            .settled_internal()
            .amount(&sentence.flow)
            .ok_or_else(|| SettlementError::UnknownFlow(sentence.flow.clone()))?;
        if *settled != expected {
            return Ok(SettlementVerdict::WrongSettlement {
                record,
                settled: settled.clone(),
                expected,
            });
        }
    }
    Ok(SettlementVerdict::Satisfied)
}

impl Bridge for SettlementBridge {
    type Left = Products;
    type Right = StockFlowInstitution<FixtureKind>;
    type Sentence = SettledProduct;
    type Verdict = SettlementVerdict;
    type Error = SettlementError;

    fn translate_sentence(
        &self,
        morphism: &JoinedSignatureMorphism<Self>,
        sentence: &SettledProduct,
    ) -> Result<SettledProduct, SettlementError> {
        let flow = morphism
            .parts()
            .right
            .map_flow(&sentence.flow)
            .cloned()
            .ok_or_else(|| SettlementError::UnknownFlow(sentence.flow.clone()))?;
        let names = &morphism.parts().left;
        Ok(SettledProduct {
            flow,
            left: Products::rename(names, &sentence.left).map_err(SettlementError::Products)?,
            right: Products::rename(names, &sentence.right).map_err(SettlementError::Products)?,
        })
    }

    fn evaluate(
        &self,
        signature: &JoinedSignature<Self>,
        model: &JoinedModel<Self>,
        sentence: &SettledProduct,
    ) -> Result<SettlementVerdict, SettlementError> {
        evaluate_settlement(signature, model, sentence)
    }

    fn is_satisfied(verdict: &SettlementVerdict) -> bool {
        verdict == &SettlementVerdict::Satisfied
    }
}

impl Bridge for StaleSettlementBridge {
    type Left = Products;
    type Right = StockFlowInstitution<FixtureKind>;
    type Sentence = SettledProduct;
    type Verdict = SettlementVerdict;
    type Error = SettlementError;

    fn translate_sentence(
        &self,
        _morphism: &JoinedSignatureMorphism<Self>,
        sentence: &SettledProduct,
    ) -> Result<SettledProduct, SettlementError> {
        Ok(sentence.clone())
    }

    fn evaluate(
        &self,
        signature: &JoinedSignature<Self>,
        model: &JoinedModel<Self>,
        sentence: &SettledProduct,
    ) -> Result<SettlementVerdict, SettlementError> {
        evaluate_settlement(signature, model, sentence)
    }

    fn is_satisfied(verdict: &SettlementVerdict) -> bool {
        verdict == &SettlementVerdict::Satisfied
    }
}

enum ReductRule {
    Faithful,
    ZeroFilled,
}

/// A comorphism of `Products` into itself along one variable map.
struct AlongMap {
    map: VariableMap,
    rule: ReductRule,
}

impl Comorphism for AlongMap {
    type Source = Products;
    type Target = Products;
    type Error = ProductError;

    fn source_institution(&self) -> &Products {
        &Products
    }

    fn target_institution(&self) -> &Products {
        &Products
    }

    fn map_signature(&self, signature: &Vocabulary) -> Result<Vocabulary, ProductError> {
        if signature != &self.map.source {
            return Err(ProductError::OutsideComorphismDomain);
        }
        Ok(self.map.target.clone())
    }

    fn map_signature_morphism(&self, morphism: &VariableMap) -> Result<VariableMap, ProductError> {
        if morphism != &Products.identity(&self.map.source)? {
            return Err(ProductError::OutsideComorphismDomain);
        }
        Products.identity(&self.map.target)
    }

    fn translate_sentence(
        &self,
        _signature: &Vocabulary,
        sentence: &Product,
    ) -> Result<Product, ProductError> {
        Products.translate_sentence(&self.map, sentence)
    }

    fn reduct(&self, _signature: &Vocabulary, model: &Values) -> Result<Values, ProductError> {
        let reduced = Products.reduct(&self.map, model)?;
        match self.rule {
            ReductRule::Faithful => Ok(reduced),
            ReductRule::ZeroFilled => Ok(Values {
                values: reduced
                    .values
                    .into_keys()
                    .map(|name| (name, q(0)))
                    .collect(),
                vocabulary: reduced.vocabulary,
            }),
        }
    }
}

fn source_vocabulary() -> Vocabulary {
    Vocabulary::new(&["price", "quantity", "spare"])
}

fn target_vocabulary() -> Vocabulary {
    Vocabulary::new(&["price", "unit_price", "quantity"])
}

/// `price -> unit_price`, `spare -> unit_price`, `quantity -> quantity`:
/// non-injective, and non-surjective because target `price` is not an image.
fn collapsing_map() -> VariableMap {
    VariableMap {
        source: source_vocabulary(),
        target: target_vocabulary(),
        map: [
            ("price", "unit_price"),
            ("spare", "unit_price"),
            ("quantity", "quantity"),
        ]
        .into_iter()
        .map(|(name, image)| (name.into(), image.into()))
        .collect(),
    }
}

fn target_values(quantity: i64) -> Values {
    Values {
        vocabulary: target_vocabulary(),
        values: [("unit_price", 3), ("price", 5), ("quantity", quantity)]
            .into_iter()
            .map(|(name, value)| (name.into(), q(value)))
            .collect(),
    }
}

fn stock_flow_model(internal: i64, equation_holds: bool) -> StockFlowModel<FixtureKind> {
    model_with_values(
        &signature(NEUTRAL),
        NEUTRAL,
        -2,
        12,
        internal,
        2,
        1,
        equation_holds,
        true,
    )
}

fn joined_model(
    quantity: i64,
    internal: i64,
    equation_holds: bool,
) -> Pair<Values, StockFlowModel<FixtureKind>> {
    Pair {
        left: target_values(quantity),
        right: stock_flow_model(internal, equation_holds),
    }
}

fn settled_product() -> SettledProduct {
    SettledProduct {
        flow: flow(NEUTRAL.flow),
        left: "price".into(),
        right: "quantity".into(),
    }
}

fn left_sentence() -> Product {
    Product::new("price", "spare", "quantity")
}

fn right_sentence() -> StockFlowSentence<FixtureKind> {
    StockFlowSentence::Transition(TransitionEquation::new(sentence("transition")))
}

fn join<B>(bridge: B) -> Join<B>
where
    B: Bridge<Left = Products, Right = StockFlowInstitution<FixtureKind>>,
{
    Join::new(Products, STOCK_FLOW, bridge)
}

fn joined_morphism<B>(join: &Join<B>) -> JoinedSignatureMorphism<B>
where
    B: Bridge<Left = Products, Right = StockFlowInstitution<FixtureKind>>,
{
    join.morphism(
        collapsing_map(),
        StockFlowRenaming::identity(&signature(NEUTRAL)),
    )
}

type SettlementSentence = JoinedSentence<Product, StockFlowSentence<FixtureKind>, SettledProduct>;

fn one_sentence_of_each_family() -> [SettlementSentence; 3] {
    [
        JoinedSentence::Left(left_sentence()),
        JoinedSentence::Right(right_sentence()),
        JoinedSentence::Bridge(settled_product()),
    ]
}

#[test]
fn joined_category_and_functor_laws_hold() {
    let join = join(SettlementBridge);
    let morphism = joined_morphism(&join);
    let source = join.source(&morphism).clone();
    let target = join.target(&morphism).clone();
    let target_identity = join.identity(&target).unwrap();
    let model = joined_model(2, 6, true);

    assert!(laws::check_signature_identity(&join, &morphism).unwrap());
    for sentence in one_sentence_of_each_family() {
        assert!(laws::check_sentence_identity(&join, &source, &sentence).unwrap());
        assert!(
            laws::check_sentence_composition(&join, &morphism, &target_identity, &sentence)
                .unwrap()
        );
    }
    assert!(laws::check_model_identity(&join, &target, &model).unwrap());
    assert!(laws::check_model_composition(&join, &morphism, &target_identity, &model).unwrap());
}

/// `(sentence, target model, expected truth value)` over the collapsing morphism.
fn square_cases() -> Vec<(
    SettlementSentence,
    Pair<Values, StockFlowModel<FixtureKind>>,
    bool,
)> {
    vec![
        (
            JoinedSentence::Bridge(settled_product()),
            joined_model(2, 6, true),
            true,
        ),
        (
            JoinedSentence::Bridge(settled_product()),
            joined_model(2, 7, true),
            false,
        ),
        (
            JoinedSentence::Left(left_sentence()),
            joined_model(1, 6, true),
            true,
        ),
        (
            JoinedSentence::Left(left_sentence()),
            joined_model(2, 6, true),
            false,
        ),
        (
            JoinedSentence::Right(right_sentence()),
            joined_model(2, 6, true),
            true,
        ),
        (
            JoinedSentence::Right(right_sentence()),
            joined_model(2, 6, false),
            false,
        ),
    ]
}

#[test]
fn joined_satisfaction_square_holds_for_each_family_with_both_truth_values() {
    let join = join(SettlementBridge);
    let morphism = joined_morphism(&join);
    for (sentence, model, expected) in square_cases() {
        let square = laws::check_satisfaction_square(&join, &morphism, &sentence, &model).unwrap();
        assert!(square.holds());
        assert_eq!(square.translated_sentence_satisfied(), expected);
        assert_eq!(square.reduced_model_satisfies_source_sentence(), expected);
    }
}

#[test]
fn joined_non_vacuity_counts_both_outcomes() {
    let join = join(SettlementBridge);
    let morphism = joined_morphism(&join);
    let target = join.target(&morphism);
    let translated = square_cases()
        .into_iter()
        .map(|(sentence, model, _)| {
            (
                join.translate_sentence(&morphism, &sentence).unwrap(),
                model,
            )
        })
        .collect::<Vec<_>>();
    let evidence = laws::check_non_vacuity(
        &join,
        translated
            .iter()
            .map(|(sentence, model)| (target, model, sentence)),
    )
    .unwrap();
    assert!(evidence.is_non_vacuous());
    assert_eq!(evidence.satisfying_cases(), 3);
    assert_eq!(evidence.falsifying_cases(), 3);
}

#[test]
fn stale_bridge_translation_breaks_the_satisfaction_square() {
    let join = join(StaleSettlementBridge);
    let morphism = joined_morphism(&join);
    let square = laws::check_satisfaction_square(
        &join,
        &morphism,
        &JoinedSentence::Bridge(settled_product()),
        &joined_model(2, 6, true),
    )
    .unwrap();
    assert!(!square.translated_sentence_satisfied());
    assert!(square.reduced_model_satisfies_source_sentence());
    assert!(!square.holds());
}

#[test]
fn embeddings_satisfy_the_comorphism_condition_with_both_truth_values() {
    let join = join(SettlementBridge);
    let neutral = signature(NEUTRAL);

    let left = join.embed_left(neutral.clone());
    let left_signature = target_vocabulary();
    let left_true = Product::new("unit_price", "unit_price", "quantity");
    let left_models = [joined_model(1, 6, true), joined_model(2, 6, true)];
    let left_true_square =
        laws::check_comorphism_satisfaction(&left, &left_signature, &left_true, &left_models[0])
            .unwrap();
    let left_false_square =
        laws::check_comorphism_satisfaction(&left, &left_signature, &left_true, &left_models[1])
            .unwrap();
    assert!(left_true_square.holds());
    assert!(left_true_square.translated_sentence_satisfied());
    assert!(left_false_square.holds());
    assert!(!left_false_square.translated_sentence_satisfied());
    assert!(
        laws::check_comorphism_non_vacuity(
            &left,
            left_models
                .iter()
                .map(|model| (&left_signature, &left_true, model)),
        )
        .unwrap()
        .is_non_vacuous()
    );
    assert_eq!(
        left.map_signature_morphism(&Products.identity(&left_signature).unwrap())
            .unwrap(),
        join.identity(&left.map_signature(&left_signature).unwrap())
            .unwrap()
    );

    let right = join.embed_right(target_vocabulary());
    let transition = right_sentence();
    let right_models = [joined_model(2, 6, true), joined_model(2, 6, false)];
    let right_true_square =
        laws::check_comorphism_satisfaction(&right, &neutral, &transition, &right_models[0])
            .unwrap();
    let right_false_square =
        laws::check_comorphism_satisfaction(&right, &neutral, &transition, &right_models[1])
            .unwrap();
    assert!(right_true_square.holds());
    assert!(right_true_square.translated_sentence_satisfied());
    assert!(right_false_square.holds());
    assert!(!right_false_square.translated_sentence_satisfied());
    assert!(
        laws::check_comorphism_non_vacuity(
            &right,
            right_models
                .iter()
                .map(|model| (&neutral, &transition, model)),
        )
        .unwrap()
        .is_non_vacuous()
    );
    assert_eq!(
        right
            .map_signature_morphism(&STOCK_FLOW.identity(&neutral).unwrap())
            .unwrap(),
        join.identity(&right.map_signature(&neutral).unwrap())
            .unwrap()
    );
}

#[test]
fn collapsing_comorphism_observes_the_satisfaction_condition() {
    let comorphism = AlongMap {
        map: collapsing_map(),
        rule: ReductRule::Faithful,
    };
    let source = source_vocabulary();
    let sentence = left_sentence();
    let models = [target_values(1), target_values(2)];

    let satisfied =
        laws::check_comorphism_satisfaction(&comorphism, &source, &sentence, &models[0]).unwrap();
    assert!(satisfied.holds());
    assert!(satisfied.translated_sentence_satisfied());
    assert!(satisfied.reduced_model_satisfies_source_sentence());

    let falsified =
        laws::check_comorphism_satisfaction(&comorphism, &source, &sentence, &models[1]).unwrap();
    assert!(falsified.holds());
    assert!(!falsified.translated_sentence_satisfied());
    assert!(!falsified.reduced_model_satisfies_source_sentence());

    assert!(
        laws::check_comorphism_non_vacuity(
            &comorphism,
            models.iter().map(|model| (&source, &sentence, model)),
        )
        .unwrap()
        .is_non_vacuous()
    );
}

#[test]
fn forgetful_comorphism_exposes_a_satisfaction_violation() {
    let comorphism = AlongMap {
        map: collapsing_map(),
        rule: ReductRule::ZeroFilled,
    };
    let square = laws::check_comorphism_satisfaction(
        &comorphism,
        &source_vocabulary(),
        &left_sentence(),
        &target_values(2),
    )
    .unwrap();
    assert!(!square.translated_sentence_satisfied());
    assert!(square.reduced_model_satisfies_source_sentence());
    assert!(!square.holds());
}

#[test]
fn joined_errors_keep_the_failing_part() {
    let join = join(SettlementBridge);
    let morphism = joined_morphism(&join);

    let missing_flow = JoinedSentence::Bridge(SettledProduct {
        flow: flow("missing"),
        ..settled_product()
    });
    assert_eq!(
        join.translate_sentence(&morphism, &missing_flow),
        Err(JoinError::Bridge(SettlementError::UnknownFlow(flow(
            "missing"
        ))))
    );

    let absent = JoinedSentence::Left(Product::new("absent", "spare", "quantity"));
    assert_eq!(
        join.translate_sentence(&morphism, &absent),
        Err(JoinError::Left(ProductError::UnknownVariable(
            "absent".into()
        )))
    );

    let economy = signature(ECONOMY);
    let foreign = Pair {
        left: target_values(2),
        right: valid_model(&economy, ECONOMY),
    };
    assert_eq!(
        join.satisfies(
            join.target(&morphism),
            &foreign,
            &JoinedSentence::Right(right_sentence()),
        ),
        Err(JoinError::Right(Error::ModelSignatureMismatch))
    );
}

#[test]
fn comorphism_errors_keep_their_side() {
    let comorphism = AlongMap {
        map: collapsing_map(),
        rule: ReductRule::Faithful,
    };
    assert_eq!(
        laws::check_comorphism_satisfaction(
            &comorphism,
            &Vocabulary::new(&["other"]),
            &left_sentence(),
            &target_values(2),
        ),
        Err(ComorphismError::Comorphism(
            ProductError::OutsideComorphismDomain
        ))
    );

    let wrong_vocabulary = Values {
        vocabulary: Vocabulary::new(&["other"]),
        ..target_values(2)
    };
    assert_eq!(
        laws::check_comorphism_satisfaction(
            &comorphism,
            &source_vocabulary(),
            &left_sentence(),
            &wrong_vocabulary,
        ),
        Err(ComorphismError::Target(ProductError::VocabularyMismatch))
    );
}
