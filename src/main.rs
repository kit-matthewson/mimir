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

    let program = mimir::Program::new(fuzzy_program, 0.01)?;

    println!("{program}");

    loop {
        // Read input from user
        print!("?> ");
        std::io::Write::flush(&mut std::io::stdout()).unwrap();
        let mut input = String::new();
        std::io::stdin().read_line(&mut input).unwrap();
        let query = input.trim();

        // Execute query and print results
        let result = program.query(query);

        let solutions = match result {
            Ok(solutions) => solutions,
            Err(e) => {
                eprintln!("{e}");
                continue;
            }
        };

        for solution in &solutions {
            for (var, val) in solution.bindings().iter() {
                println!("  {} = {}", var.name(), val);
            }

            println!(
                "  {}.",
                match solution.truth_value() {
                    x if x >= 0.99 => "true".to_string(),
                    x if x <= 0.01 => "false".to_string(),
                    x => format!("{:.2}", x),
                },
            );
        }

        if solutions.is_empty() {
            println!("  false.");
        }
    }
}
