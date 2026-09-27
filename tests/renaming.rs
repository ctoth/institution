//! The generic injective renaming, over a toy vocabulary of declared names.

use std::collections::BTreeMap;

use institution::renaming::{Renaming, RenamingError, Vocabulary};

/// Names, each declared with a sort. A renaming must keep every sort.
#[derive(Clone, Debug, PartialEq)]
struct Names(BTreeMap<&'static str, u8>);

#[derive(Debug, PartialEq)]
enum NamesError {
    Renaming(RenamingError<&'static str>),
    SortChanged {
        from: &'static str,
        to: &'static str,
    },
}

impl From<RenamingError<&'static str>> for NamesError {
    fn from(error: RenamingError<&'static str>) -> Self {
        Self::Renaming(error)
    }
}

impl Vocabulary for Names {
    type Symbol = &'static str;
    type Error = NamesError;

    fn symbols(&self) -> Vec<&'static str> {
        self.0.keys().copied().collect()
    }

    fn check(renaming: &Renaming<Self>) -> Result<(), NamesError> {
        for (from, to) in renaming.pairs() {
            if renaming.source().0[from] != renaming.target().0[to] {
                return Err(NamesError::SortChanged { from, to });
            }
        }
        Ok(())
    }
}

fn names(entries: &[(&'static str, u8)]) -> Names {
    Names(entries.iter().copied().collect())
}

#[test]
fn a_renaming_forgets_the_target_names_outside_its_image() {
    let source = names(&[("a", 1), ("b", 2)]);
    let target = names(&[("x", 1), ("y", 2), ("z", 1)]);
    let renaming = Renaming::new(source, target, [("b", "y"), ("a", "x")]).unwrap();

    assert_eq!(renaming.image(&"a"), Some(&"x"));
    assert_eq!(renaming.image(&"b"), Some(&"y"));
    assert_eq!(renaming.preimage(&"y"), Some(&"b"));
    assert_eq!(renaming.preimage(&"z"), None);
    assert_eq!(
        renaming.pairs().collect::<Vec<_>>(),
        [(&"a", &"x"), (&"b", &"y")]
    );
}

#[test]
fn a_renaming_is_total_injective_and_stays_inside_both_vocabularies() {
    let source = names(&[("a", 1), ("b", 1)]);
    let target = names(&[("x", 1), ("y", 1)]);
    let new = |pairs: &[(&'static str, &'static str)]| {
        Renaming::new(source.clone(), target.clone(), pairs.iter().copied())
    };

    assert_eq!(
        new(&[("a", "x")]),
        Err(NamesError::Renaming(RenamingError::Unnamed("b")))
    );
    assert_eq!(
        new(&[("a", "x"), ("b", "x")]),
        Err(NamesError::Renaming(RenamingError::NotInjective("x")))
    );
    assert_eq!(
        new(&[("a", "x"), ("a", "y"), ("b", "y")]),
        Err(NamesError::Renaming(RenamingError::Repeated("a")))
    );
    assert_eq!(
        new(&[("a", "x"), ("c", "y")]),
        Err(NamesError::Renaming(RenamingError::NotInSource("c")))
    );
    assert_eq!(
        new(&[("a", "x"), ("b", "w")]),
        Err(NamesError::Renaming(RenamingError::NotInTarget("w")))
    );
}

#[test]
fn the_vocabulary_says_what_else_a_renaming_preserves() {
    let source = names(&[("a", 1)]);
    let target = names(&[("x", 2), ("y", 1)]);
    assert_eq!(
        Renaming::new(source.clone(), target.clone(), [("a", "x")]),
        Err(NamesError::SortChanged { from: "a", to: "x" })
    );
    assert!(Renaming::new(source, target, [("a", "y")]).is_ok());
}

#[test]
fn identity_and_composition_follow_the_symbol_maps() {
    let first_source = names(&[("a", 1)]);
    let middle = names(&[("m", 1), ("n", 2)]);
    let last = names(&[("x", 1), ("y", 2), ("z", 1)]);
    let first = Renaming::new(first_source.clone(), middle.clone(), [("a", "m")]).unwrap();
    let second = Renaming::new(middle.clone(), last.clone(), [("m", "z"), ("n", "y")]).unwrap();

    let composite = first.compose(&second).unwrap();
    assert_eq!(composite.source(), &first_source);
    assert_eq!(composite.target(), &last);
    assert_eq!(composite.pairs().collect::<Vec<_>>(), [(&"a", &"z")]);

    let identity = Renaming::identity(&middle).unwrap();
    assert_eq!(identity.compose(&second).unwrap(), second);
    assert_eq!(first.compose(&identity).unwrap(), first);

    assert_eq!(
        second.compose(&first),
        Err(NamesError::Renaming(RenamingError::NotComposable))
    );
}
