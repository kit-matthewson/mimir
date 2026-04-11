fn main() -> Result<(), mimir::MimirError> {
    let fuzzy_program = r"
edge(a, b).
edge(b, c) :~ 0.9.
edge(c, d).
edge(c, e) :~ 0.8.

path(A, B) :- edge(A, B).
path(A, B) :- edge(A, X), path(X, B).
";

    let program = mimir::Program::new(fuzzy_program)?;

    println!("{fuzzy_program}");

    loop {
        // Read input from user
        let mut input = String::new();
        print!("\n?>");
        std::io::Write::flush(&mut std::io::stdout()).expect("Failed to flush stdout");
        std::io::stdin()
            .read_line(&mut input)
            .expect("Failed to read input");
        let query = input.trim();

        // If the first char is ~, strip it and treat as a fuzzy query
        let (query, fuzzy) = if let Some(stripped) = query.strip_prefix('~') {
            (stripped.trim(), true)
        } else {
            (query, false)
        };

        // Execute query and print results
        let result = if fuzzy {
            program.fuzzy_query(query, 0.01)
        } else {
            program.crisp_query(query)
        };

        let solutions = match result {
            Ok(solutions) => solutions,
            Err(e) => {
                eprintln!("{e}");
                return Ok(());
            }
        };

        for solution in &solutions {
            if solution.bindings().is_empty() {
                if fuzzy {
                    println!("  1.00.");
                } else {
                    println!("  true.");
                }

                continue;
            }

            print!(" ");

            for (i, (var, val)) in solution.bindings().iter().enumerate() {
                if i > 0 {
                    print!(", ");
                }

                print!("{} = {}", var.name(), val);
            }

            if fuzzy {
                print!("  {:.2}.", solution.truth_value());
            }

            println!();
        }

        if solutions.is_empty() {
            println!(" false.");
        }
    }
}
