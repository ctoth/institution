use std::collections::{BTreeMap, BTreeSet};

use institution::{Institution, laws};

#[derive(Clone, Debug, Eq, PartialEq)]
struct Signature(BTreeSet<String>);

impl Signature {
    fn new(symbols: &[&str]) -> Self {
        Self(symbols.iter().map(|symbol| String::from(*symbol)).collect())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Morphism {
    source: Signature,
    target: Signature,
    symbols: BTreeMap<String, String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Model {
    signature: Signature,
    true_atoms: BTreeSet<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum TestError {
    SignatureMismatch,
    MorphismDomainMismatch,
    MorphismTargetOutsideSignature(String),
    InvalidModelAtom(String),
    UnknownSymbol(String),
    NonComposableMorphisms,
}

struct PropositionalLogic;

impl PropositionalLogic {
    fn validate_morphism(morphism: &Morphism) -> Result<(), TestError> {
        if !morphism.symbols.keys().eq(morphism.source.0.iter()) {
            return Err(TestError::MorphismDomainMismatch);
        }

        if let Some(symbol) = morphism
            .symbols
            .values()
            .find(|symbol| !morphism.target.0.contains(*symbol))
        {
            return Err(TestError::MorphismTargetOutsideSignature(symbol.clone()));
        }

        Ok(())
    }

    fn validate_model(signature: &Signature, model: &Model) -> Result<(), TestError> {
        if &model.signature != signature {
            return Err(TestError::SignatureMismatch);
        }

        if let Some(atom) = model
            .true_atoms
            .iter()
            .find(|atom| !signature.0.contains(*atom))
        {
            return Err(TestError::InvalidModelAtom(atom.clone()));
        }

        Ok(())
    }
}

impl Institution for PropositionalLogic {
    type Signature = Signature;
    type SignatureMorphism = Morphism;
    type Sentence = String;
    type Model = Model;
    type Error = TestError;

    fn source<'a>(&self, morphism: &'a Self::SignatureMorphism) -> &'a Self::Signature {
        &morphism.source
    }

    fn target<'a>(&self, morphism: &'a Self::SignatureMorphism) -> &'a Self::Signature {
        &morphism.target
    }

    fn identity(
        &self,
        signature: &Self::Signature,
    ) -> Result<Self::SignatureMorphism, Self::Error> {
        Ok(Morphism {
            source: signature.clone(),
            target: signature.clone(),
            symbols: signature
                .0
                .iter()
                .map(|symbol| (symbol.clone(), symbol.clone()))
                .collect(),
        })
    }

    fn compose(
        &self,
        first: &Self::SignatureMorphism,
        second: &Self::SignatureMorphism,
    ) -> Result<Self::SignatureMorphism, Self::Error> {
        Self::validate_morphism(first)?;
        Self::validate_morphism(second)?;
        if first.target != second.source {
            return Err(TestError::NonComposableMorphisms);
        }
        let symbols = first
            .symbols
            .iter()
            .map(|(source, middle)| {
                second
                    .symbols
                    .get(middle)
                    .cloned()
                    .map(|target| (source.clone(), target))
                    .ok_or_else(|| TestError::UnknownSymbol(middle.clone()))
            })
            .collect::<Result<_, _>>()?;
        Ok(Morphism {
            source: first.source.clone(),
            target: second.target.clone(),
            symbols,
        })
    }

    fn translate_sentence(
        &self,
        morphism: &Self::SignatureMorphism,
        sentence: &Self::Sentence,
    ) -> Result<Self::Sentence, Self::Error> {
        Self::validate_morphism(morphism)?;

        if !morphism.source.0.contains(sentence) {
            return Err(TestError::UnknownSymbol(sentence.clone()));
        }

        morphism
            .symbols
            .get(sentence)
            .cloned()
            .ok_or_else(|| TestError::UnknownSymbol(sentence.clone()))
    }

    fn reduct(
        &self,
        morphism: &Self::SignatureMorphism,
        model: &Self::Model,
    ) -> Result<Self::Model, Self::Error> {
        Self::validate_morphism(morphism)?;
        Self::validate_model(&morphism.target, model)?;

        let true_atoms = morphism
            .symbols
            .iter()
            .filter(|(_, target)| model.true_atoms.contains(*target))
            .map(|(source, _)| source.clone())
            .collect();

        Ok(Model {
            signature: morphism.source.clone(),
            true_atoms,
        })
    }

    fn satisfies(
        &self,
        signature: &Self::Signature,
        model: &Self::Model,
        sentence: &Self::Sentence,
    ) -> Result<bool, Self::Error> {
        Self::validate_model(signature, model)?;

        if !signature.0.contains(sentence) {
            return Err(TestError::UnknownSymbol(sentence.clone()));
        }

        Ok(model.true_atoms.contains(sentence))
    }
}

struct NonCommutingLogic;

impl Institution for NonCommutingLogic {
    type Signature = Signature;
    type SignatureMorphism = Morphism;
    type Sentence = String;
    type Model = Model;
    type Error = TestError;

    fn source<'a>(&self, morphism: &'a Self::SignatureMorphism) -> &'a Self::Signature {
        PropositionalLogic.source(morphism)
    }

    fn target<'a>(&self, morphism: &'a Self::SignatureMorphism) -> &'a Self::Signature {
        PropositionalLogic.target(morphism)
    }

    fn identity(
        &self,
        signature: &Self::Signature,
    ) -> Result<Self::SignatureMorphism, Self::Error> {
        PropositionalLogic.identity(signature)
    }

    fn compose(
        &self,
        first: &Self::SignatureMorphism,
        second: &Self::SignatureMorphism,
    ) -> Result<Self::SignatureMorphism, Self::Error> {
        PropositionalLogic.compose(first, second)
    }

    fn translate_sentence(
        &self,
        morphism: &Self::SignatureMorphism,
        sentence: &Self::Sentence,
    ) -> Result<Self::Sentence, Self::Error> {
        PropositionalLogic.translate_sentence(morphism, sentence)
    }

    fn reduct(
        &self,
        morphism: &Self::SignatureMorphism,
        model: &Self::Model,
    ) -> Result<Self::Model, Self::Error> {
        let mut reduced = PropositionalLogic.reduct(morphism, model)?;
        reduced.true_atoms.clear();
        Ok(reduced)
    }

    fn satisfies(
        &self,
        signature: &Self::Signature,
        model: &Self::Model,
        sentence: &Self::Sentence,
    ) -> Result<bool, Self::Error> {
        PropositionalLogic.satisfies(signature, model, sentence)
    }
}

fn fixture() -> (PropositionalLogic, Morphism, Model, String) {
    let source = Signature::new(&["p"]);
    let target = Signature::new(&["q"]);
    let morphism = Morphism {
        source,
        target: target.clone(),
        symbols: BTreeMap::from([(String::from("p"), String::from("q"))]),
    };
    let model = Model {
        signature: target,
        true_atoms: BTreeSet::from([String::from("q")]),
    };

    (PropositionalLogic, morphism, model, String::from("p"))
}

fn chain() -> (Morphism, Morphism, Morphism, Model, String) {
    let a = Signature::new(&["p"]);
    let b = Signature::new(&["q"]);
    let c = Signature::new(&["r"]);
    let d = Signature::new(&["s"]);
    let first = Morphism {
        source: a,
        target: b.clone(),
        symbols: BTreeMap::from([(String::from("p"), String::from("q"))]),
    };
    let second = Morphism {
        source: b,
        target: c.clone(),
        symbols: BTreeMap::from([(String::from("q"), String::from("r"))]),
    };
    let third = Morphism {
        source: c,
        target: d.clone(),
        symbols: BTreeMap::from([(String::from("r"), String::from("s"))]),
    };
    let model = Model {
        signature: d,
        true_atoms: BTreeSet::from([String::from("s")]),
    };
    (first, second, third, model, String::from("p"))
}

#[test]
fn signature_category_and_sentence_model_functor_laws_hold() -> Result<(), TestError> {
    let institution = PropositionalLogic;
    let (first, second, third, target_model, source_sentence) = chain();

    assert!(laws::check_signature_identity(&institution, &first)?);
    assert!(laws::check_signature_associativity(
        &institution,
        &first,
        &second,
        &third,
    )?);
    assert!(laws::check_sentence_identity(
        &institution,
        &first.source,
        &source_sentence,
    )?);
    assert!(laws::check_sentence_composition(
        &institution,
        &first,
        &second,
        &source_sentence,
    )?);
    assert!(laws::check_model_identity(
        &institution,
        &third.target,
        &target_model,
    )?);
    assert!(laws::check_model_composition(
        &institution,
        &second,
        &third,
        &target_model,
    )?);
    Ok(())
}

#[test]
fn satisfaction_square_commutes() -> Result<(), TestError> {
    let (institution, morphism, target_model, source_sentence) = fixture();

    let square =
        laws::check_satisfaction_square(&institution, &morphism, &source_sentence, &target_model)?;

    assert!(square.holds());
    assert!(square.translated_sentence_satisfied());
    assert!(square.reduced_model_satisfies_source_sentence());
    Ok(())
}

#[test]
fn satisfaction_square_commutes_when_both_observations_are_false() -> Result<(), TestError> {
    let (institution, morphism, mut target_model, source_sentence) = fixture();
    target_model.true_atoms.clear();

    let square =
        laws::check_satisfaction_square(&institution, &morphism, &source_sentence, &target_model)?;

    assert!(square.holds());
    assert!(!square.translated_sentence_satisfied());
    assert!(!square.reduced_model_satisfies_source_sentence());
    Ok(())
}

#[test]
fn satisfaction_square_exposes_a_law_violation() -> Result<(), TestError> {
    let (_, morphism, target_model, source_sentence) = fixture();

    let square = laws::check_satisfaction_square(
        &NonCommutingLogic,
        &morphism,
        &source_sentence,
        &target_model,
    )?;

    assert!(!square.holds());
    assert!(square.translated_sentence_satisfied());
    assert!(!square.reduced_model_satisfies_source_sentence());
    Ok(())
}

#[test]
fn non_vacuity_requires_both_truth_values() -> Result<(), TestError> {
    let signature = Signature::new(&["p"]);
    let true_model = Model {
        signature: signature.clone(),
        true_atoms: BTreeSet::from([String::from("p")]),
    };
    let false_model = Model {
        signature: signature.clone(),
        true_atoms: BTreeSet::new(),
    };
    let sentence = String::from("p");
    let institution = PropositionalLogic;

    let evidence = laws::check_non_vacuity(
        &institution,
        [
            (&signature, &true_model, &sentence),
            (&signature, &false_model, &sentence),
        ],
    )?;

    assert!(evidence.is_non_vacuous());
    assert_eq!(evidence.satisfying_cases(), 1);
    assert_eq!(evidence.falsifying_cases(), 1);
    Ok(())
}

#[test]
fn one_sided_examples_are_reported_as_vacuous() -> Result<(), TestError> {
    let signature = Signature::new(&["p"]);
    let model = Model {
        signature: signature.clone(),
        true_atoms: BTreeSet::from([String::from("p")]),
    };
    let sentence = String::from("p");

    let evidence = laws::check_non_vacuity(&PropositionalLogic, [(&signature, &model, &sentence)])?;

    assert!(!evidence.is_non_vacuous());
    Ok(())
}

#[test]
fn empty_examples_are_reported_as_vacuous() -> Result<(), TestError> {
    let evidence = laws::check_non_vacuity(
        &PropositionalLogic,
        std::iter::empty::<(&Signature, &Model, &String)>(),
    )?;

    assert!(!evidence.is_non_vacuous());
    assert_eq!(evidence.satisfying_cases(), 0);
    assert_eq!(evidence.falsifying_cases(), 0);
    Ok(())
}

#[test]
fn malformed_source_sentence_is_rejected() {
    let (institution, morphism, target_model, _) = fixture();
    let malformed = String::from("not-in-source");

    assert_eq!(
        institution.translate_sentence(&morphism, &malformed),
        Err(TestError::UnknownSymbol(malformed.clone()))
    );
    assert_eq!(
        laws::check_satisfaction_square(&institution, &morphism, &malformed, &target_model),
        Err(TestError::UnknownSymbol(malformed))
    );
}

#[test]
fn target_model_signature_mismatch_is_rejected() {
    let (institution, morphism, mut target_model, source_sentence) = fixture();
    target_model.signature = Signature::new(&["different"]);

    assert_eq!(
        laws::check_satisfaction_square(&institution, &morphism, &source_sentence, &target_model),
        Err(TestError::SignatureMismatch)
    );
}

#[test]
fn morphism_domain_must_exactly_match_the_source_signature() {
    let (institution, mut morphism, target_model, source_sentence) = fixture();
    morphism
        .symbols
        .insert(String::from("outside"), String::from("q"));

    assert_eq!(
        institution.translate_sentence(&morphism, &source_sentence),
        Err(TestError::MorphismDomainMismatch)
    );
    assert_eq!(
        institution.reduct(&morphism, &target_model),
        Err(TestError::MorphismDomainMismatch)
    );

    morphism.symbols.clear();
    assert_eq!(
        institution.translate_sentence(&morphism, &source_sentence),
        Err(TestError::MorphismDomainMismatch)
    );
    assert_eq!(
        institution.reduct(&morphism, &target_model),
        Err(TestError::MorphismDomainMismatch)
    );
}

#[test]
fn morphism_images_must_belong_to_the_target_signature() {
    let (institution, mut morphism, target_model, source_sentence) = fixture();
    morphism
        .symbols
        .insert(String::from("p"), String::from("outside"));

    let expected = TestError::MorphismTargetOutsideSignature(String::from("outside"));
    assert_eq!(
        institution.translate_sentence(&morphism, &source_sentence),
        Err(expected.clone())
    );
    assert_eq!(institution.reduct(&morphism, &target_model), Err(expected));
}

#[test]
fn true_atoms_must_belong_to_the_model_signature() {
    let (institution, morphism, mut target_model, source_sentence) = fixture();
    target_model.true_atoms.insert(String::from("outside"));

    let expected = TestError::InvalidModelAtom(String::from("outside"));
    assert_eq!(
        institution.satisfies(&morphism.target, &target_model, &String::from("q")),
        Err(expected.clone())
    );
    assert_eq!(institution.reduct(&morphism, &target_model), Err(expected));

    assert_eq!(
        laws::check_satisfaction_square(&institution, &morphism, &source_sentence, &target_model),
        Err(TestError::InvalidModelAtom(String::from("outside")))
    );
}

#[test]
fn non_vacuity_propagates_satisfaction_errors() {
    let signature = Signature::new(&["p"]);
    let malformed_model = Model {
        signature: signature.clone(),
        true_atoms: BTreeSet::from([String::from("outside")]),
    };
    let sentence = String::from("p");

    assert_eq!(
        laws::check_non_vacuity(
            &PropositionalLogic,
            [(&signature, &malformed_model, &sentence)]
        ),
        Err(TestError::InvalidModelAtom(String::from("outside")))
    );
}
