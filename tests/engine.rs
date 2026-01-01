use mimir::{clause, engine::*, var_vec};

#[test]
fn test_engine_simple_query() -> Result<(), mimir::error::EngineError> {
    let program = vec![
        clause!(is_ten(T1) { T2 } :- Goal::Conjunction(
            Box::new(Goal::Assign(Variable::new("T2"), RHSTerm::Num(10))),
            Box::new(Goal::Equivalence(Variable::new("T1"), Variable::new("T2")))
        )),
        clause!(is_ten_or_five(T1) { T2 } :- Goal::Disjunction(
                    Box::new(Goal::Check {
                        functor: "is_ten".to_string(),
                        params: var_vec!["T1"],
                    }),
                    Box::new(Goal::Conjunction(
                        Box::new(Goal::Assign(Variable::new("T2"), RHSTerm::Num(5))),
                        Box::new(Goal::Equivalence(Variable::new("T1"), Variable::new("T2")))
                    ))
                )
        ),
    ];

    let engine = Engine::new(program);

    let query = Query {
        local_vars: var_vec!["X"],
        goal: Goal::Check {
            functor: "is_ten_or_five".to_string(),
            params: var_vec!["X"],
        },
    };

    let solutions = engine.execute(query.clone())?;

    let mut results = vec![];
    for solution in solutions.iter() {
        let value = solution.0.get(&Variable::new("X"), &solution.1)?;
        results.push(value);
    }

    assert!(results.contains(&Value::Number(10)));
    assert!(results.contains(&Value::Number(5)));
    assert_eq!(results.len(), 2);

    Ok(())
}
