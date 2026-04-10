use ordered_float::OrderedFloat;

fn main() -> Result<(), mimir::error::MimirError> {
    let fuzzy_program = r"
trapezoidal(X, A, _, _, _, Y) :-
    X < A,
    Y = 0.
trapezoidal(X, A, B, _, _, Y) :-
    X >= A,
    X <= B,
    Y = (X - A) / (B - A).
trapezoidal(X, _, B, C, _, Y) :-
    X > B,
    X < C,
    Y = 1.
trapezoidal(X, _, _, C, D, Y) :-
    X >= C,
    X <= D,
    Y = (D - X) / (D - C).
trapezoidal(X, _, _, _, D, Y) :-
    X > D,
    Y = 0.
warm(X) :~
    trapezoidal(X, 15, 20, 25, 30, Y),
    Y.
    ";

    println!(
        r"
warm(X) :~
    trapezoidal(X, 15, 20, 25, 30, Y),
    Y.
    "
    );

    loop {
        print!("temperature = ");
        std::io::Write::flush(&mut std::io::stdout()).unwrap(); // Ensure prompt is printed before input
        let mut input = String::new();
        std::io::stdin().read_line(&mut input).unwrap();
        let input = input.trim();
        let temp: f64 = input.parse().expect("Please enter a valid number");

        let query = mimir::engine::Query {
            local_vars: mimir::var_vec!["X"],
            goal: mimir::engine::Goal::Conjunction(
                Box::new(mimir::engine::Goal::Assign(
                    mimir::engine::Variable::new("X"),
                    mimir::engine::RHSTerm::Num(OrderedFloat::from(temp)),
                )),
                Box::new(mimir::engine::Goal::Check {
                    functor: "warm".to_string(),
                    params: mimir::var_vec!["X"],
                }),
            ),
        };

        let (_, user_program) = mimir::parser::program(fuzzy_program).unwrap();
        let program = user_program
            .into_iter()
            .map(mimir::translator::translate)
            .collect::<Result<Vec<_>, _>>()?;

        let engine = mimir::engine::Engine::new(program, 0.01);
        let solutions = engine.execute(query.clone())?;

        if solutions.is_empty() {
            println!("warm({}) ~ 0.00", temp);
        } else {
            for solution in solutions.iter() {
                let truth = solution.truth_value();
                println!("warm({}) ~ {:.2}", temp, truth);
            }
        }

        println!();
    }
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
        let solution = &solutions[0];
        let value = solution.get(&mimir::engine::Variable::new("X")).unwrap();
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
        let solution = &solutions[0];
        let value = solution.get(&mimir::engine::Variable::new("X")).unwrap();
        assert_eq!(
            value,
            mimir::engine::Value::Number(OrderedFloat::from(11.0))
        );
    }
}
