use mimir::{engine::*, error::EngineError, var_vec};

macro_rules! clause {
    ($name:ident ( $($p:ident),* ) { $($l:ident),* } :- $goal:expr) => {
        Clause::new(
            Symbol::new(
                stringify!($name),
                vec![$( Variable::new(stringify!($p)) ),*],
                vec![$( Variable::new(stringify!($l)) ),*],
            ),
            $goal
        )
    };
}

fn main() -> Result<(), EngineError> {
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

    for clause in &program {
        println!("{}", clause);
    }

    let engine = Engine::new(program);

    let query = Query {
        local_vars: var_vec!["X"],
        goal: Goal::Check {
            functor: "is_ten_or_five".to_string(),
            params: var_vec!["X"],
        },
    };

    println!("\n{}", query);

    let solutions = engine.execute(query.clone())?;

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
