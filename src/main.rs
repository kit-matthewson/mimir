use mimir::{engine::Query, var_vec};
use ordered_float::OrderedFloat;

fn main() -> Result<(), mimir::error::MimirError> {
    let program = r"
is_ten(X) :- X = 10.
is_ten_or_five(X) :- X = 10.
is_ten_or_five(X) :- X = 5.
is_gt_ten(X) :- X > 10.
    ";

    println!("{}", program);

    let query = mimir::engine::Query {
        local_vars: var_vec!["X"],
        goal: mimir::engine::Goal::Check {
            functor: "is_ten".to_string(),
            params: mimir::var_vec!["X"],
        },
    };
    execute(program, query)?;
    println!();

    let query = mimir::engine::Query {
        local_vars: var_vec!["X"],
        goal: mimir::engine::Goal::Check {
            functor: "is_ten_or_five".to_string(),
            params: var_vec!["X"],
        },
    };
    execute(program, query)?;
    println!();

    let query = mimir::engine::Query {
        local_vars: mimir::var_vec!["X"],
        goal: mimir::engine::Goal::Conjunction(
            Box::new(mimir::engine::Goal::Assign(
                mimir::engine::Variable::new("X"),
                mimir::engine::RHSTerm::Num(OrderedFloat::from(5.0)),
            )),
            Box::new(mimir::engine::Goal::Check {
                functor: "is_gt_ten".to_string(),
                params: mimir::var_vec!["X"],
            }),
        ),
    };
    execute(program, query)?;

    Ok(())
}

fn execute(program: &str, query: Query) -> Result<(), mimir::error::MimirError> {
    let (_, user_program) = mimir::parser::program(program).unwrap();
    let program = user_program
        .into_iter()
        .map(mimir::translator::translate)
        .collect::<Result<Vec<_>, _>>()?;

    // for clause in &program {
    //     // println!("{}", clause);
    // }

    let engine = mimir::engine::Engine::new(program, 0.01);
    let solutions = engine.execute(query.clone())?;

    println!("{}", query);
    if solutions.is_empty() {
        println!("  false.");
        return Ok(());
    }

    for solution in solutions.iter() {
        print!("  ");
        for var in &query.local_vars {
            let value = solution.0.get(var, &solution.1)?;
            print!("{} = {:?}", var, value);
            if var != query.local_vars.last().unwrap() {
                print!(", ");
            }
        }
        println!();
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use ordered_float::OrderedFloat;

    #[test]
    fn test_is_ten() {
        let input = "is_ten(X) :- X = 10.";
        let (_, user_program) = mimir::parser::clause(input).unwrap();
        let program = mimir::translator::translate(user_program).unwrap();

        let query = mimir::engine::Query {
            local_vars: mimir::var_vec!["X"],
            goal: mimir::engine::Goal::Check {
                functor: "is_ten".to_string(),
                params: mimir::var_vec!["X"],
            },
        };

        let engine = mimir::engine::Engine::new(vec![program], 0.01);
        let solutions = engine.execute(query).unwrap();

        assert_eq!(solutions.len(), 1);
        let (env, equiv) = &solutions[0];
        let value = env.get(&mimir::engine::Variable::new("X"), equiv).unwrap();
        assert_eq!(
            value,
            mimir::engine::Value::Number(OrderedFloat::from(10.0))
        );
    }

    #[test]
    fn test_is_gt_ten() {
        let input = "is_gt_ten(X) :- X > 10.";
        let (_, user_program) = mimir::parser::clause(input).unwrap();
        let program = mimir::translator::translate(user_program).unwrap();

        let query = mimir::engine::Query {
            local_vars: mimir::var_vec!["X"],
            goal: mimir::engine::Goal::Conjunction(
                Box::new(mimir::engine::Goal::Assign(
                    mimir::engine::Variable::new("X"),
                    mimir::engine::RHSTerm::Num(OrderedFloat::from(11.0)),
                )),
                Box::new(mimir::engine::Goal::Check {
                    functor: "is_gt_ten".to_string(),
                    params: mimir::var_vec!["X"],
                }),
            ),
        };

        let engine = mimir::engine::Engine::new(vec![program], 0.01);
        let solutions = engine.execute(query).unwrap();

        assert_eq!(solutions.len(), 1);
        let (env, equiv) = &solutions[0];
        let value = env.get(&mimir::engine::Variable::new("X"), equiv).unwrap();
        assert_eq!(
            value,
            mimir::engine::Value::Number(OrderedFloat::from(11.0))
        );
    }
}
