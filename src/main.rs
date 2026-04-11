fn main() -> Result<(), mimir::MimirError> {
    let fuzzy_program = r"
edge(a, b).
edge(b, c).
edge(c, d).
edge(c, e).

path(A, B) :- edge(A, B).
path(A, B) :- edge(A, X), path(X, B).
";

    let program = mimir::Program::new(fuzzy_program)?;

    println!("{program}");

    loop {
        // Read input from user
        let mut input = String::new();
        print!("?>");
        std::io::Write::flush(&mut std::io::stdout()).expect("Failed to flush stdout");
        std::io::stdin()
            .read_line(&mut input)
            .expect("Failed to read input");
        let query = input.trim();

        // Execute query and print results
        let result = program.query(query, 0.01);

        let solutions = match result {
            Ok(solutions) => solutions,
            Err(e) => {
                eprintln!("{e}");
                return Ok(());
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
