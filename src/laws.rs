//! Reusable observations for individual satisfaction squares and test cases.
//!
//! These helpers execute supplied operations and do not prove institution laws
//! universally. Implementations remain responsible for deterministic behavior,
//! input well-formedness, signature-category laws, and functoriality laws.

use crate::Institution;

/// The two satisfaction observations made for one supplied square.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SatisfactionSquare {
    translated_sentence_satisfied: bool,
    reduced_model_satisfies_source_sentence: bool,
}

impl SatisfactionSquare {
    /// Whether the two observations made for this square agree.
    #[must_use]
    pub fn holds(self) -> bool {
        self.translated_sentence_satisfied == self.reduced_model_satisfies_source_sentence
    }

    /// Satisfaction at the target after translating the source sentence.
    #[must_use]
    pub fn translated_sentence_satisfied(self) -> bool {
        self.translated_sentence_satisfied
    }

    /// Satisfaction at the source after reducing the target model.
    #[must_use]
    pub fn reduced_model_satisfies_source_sentence(self) -> bool {
        self.reduced_model_satisfies_source_sentence
    }
}

/// Evaluates both sides of one candidate Goguen satisfaction square.
///
/// Given `morphism: source -> target`, a source sentence, and a target model,
/// this observes the equation
/// `target_model |= translate(sentence)` iff
/// `reduct(target_model) |= sentence`.
///
/// For deterministic operations and well-formed inputs, [`SatisfactionSquare::holds`]
/// reports agreement for this case only. It is not proof that the satisfaction
/// condition holds for all morphisms, sentences, and models. Operation errors
/// are returned without being converted into a law result.
pub fn check_satisfaction_square<I>(
    institution: &I,
    morphism: &I::SignatureMorphism,
    source_sentence: &I::Sentence,
    target_model: &I::Model,
) -> Result<SatisfactionSquare, I::Error>
where
    I: Institution,
{
    let translated = institution.translate_sentence(morphism, source_sentence)?;
    let translated_sentence_satisfied =
        institution.satisfies(institution.target(morphism), target_model, &translated)?;

    let reduced = institution.reduct(morphism, target_model)?;
    let reduced_model_satisfies_source_sentence =
        institution.satisfies(institution.source(morphism), &reduced, source_sentence)?;

    Ok(SatisfactionSquare {
        translated_sentence_satisfied,
        reduced_model_satisfies_source_sentence,
    })
}

/// Counts observed positive and negative supplied satisfaction examples.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct NonVacuity {
    satisfying_cases: usize,
    falsifying_cases: usize,
}

impl NonVacuity {
    /// Whether the supplied examples exercise both outcomes of satisfaction.
    #[must_use]
    pub fn is_non_vacuous(self) -> bool {
        self.satisfying_cases > 0 && self.falsifying_cases > 0
    }

    /// The number of examples for which satisfaction holds.
    #[must_use]
    pub fn satisfying_cases(self) -> usize {
        self.satisfying_cases
    }

    /// The number of examples for which satisfaction does not hold.
    #[must_use]
    pub fn falsifying_cases(self) -> usize {
        self.falsifying_cases
    }
}

/// Evaluates supplied satisfaction examples and counts their observed outcomes.
///
/// The returned evidence is called non-vacuous when these well-formed,
/// deterministic cases include at least one satisfying and one falsifying
/// observation. Empty and one-sided inputs are reported as vacuous. This helper
/// cannot establish that the satisfaction relation is globally non-vacuous.
/// Operation errors are returned immediately.
pub fn check_non_vacuity<'a, I, Cases>(
    institution: &I,
    cases: Cases,
) -> Result<NonVacuity, I::Error>
where
    I: Institution + 'a,
    I::Signature: 'a,
    I::Model: 'a,
    I::Sentence: 'a,
    Cases: IntoIterator<Item = (&'a I::Signature, &'a I::Model, &'a I::Sentence)>,
{
    let mut evidence = NonVacuity::default();

    for (signature, model, sentence) in cases {
        if institution.satisfies(signature, model, sentence)? {
            evidence.satisfying_cases += 1;
        } else {
            evidence.falsifying_cases += 1;
        }
    }

    Ok(evidence)
}
