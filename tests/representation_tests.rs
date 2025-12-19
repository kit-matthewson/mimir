use std::collections::HashSet;

use mimir::engine::representation::*;

#[test]
fn test_placeholder_gen() {
    let mut used = HashSet::new();

    let mut pgen = PlaceholderGenerator::new();

    for _ in 0..100 {
        let new = pgen.new_placeholder();
        assert!(!used.contains(&new));
        used.insert(new);
    }
}

#[test]
fn test_unification() {
    let mut equiv = Equivalence::new();
    let mut pgen = PlaceholderGenerator::new();

    let x = pgen.new_placeholder();
    let y = pgen.new_placeholder();

    equiv.unify(&x, &Value::Number(42)).unwrap();
    equiv.unify(&y, &x).unwrap();

    assert_eq!(equiv.set_representative(&y).unwrap(), Value::Number(42));
}

#[test]
fn test_unification_fails() {
    let mut equiv = Equivalence::new();

    let x = Value::Number(5);
    let y = Value::Number(10);

    assert!(equiv.unify(&x, &y).is_err());
}
