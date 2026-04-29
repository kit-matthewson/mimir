use std::{
    env, fs,
    io::{self, Write},
};

fn main() -> Result<(), mimir::MimirError> {
    // Read and display the program file
    let program_path = env::args().nth(1).expect("usage: mimir <program_file>");

    let program_source = fs::read_to_string(&program_path).expect("failed to read program file");
    let program = mimir::Program::new(&program_source)?;

    println!("Loaded program from {program_path}:");
    println!("{}", program);
    println!();

    println!("Enter queries with optional leading ~ for fuzzy execution.");
    println!("Type exit. to leave.");
    println!();

    let stdin = io::stdin();
    let mut input = String::new();

    loop {
        // Get user input
        print!("?- ");
        io::stdout().flush().expect("failed to flush stdout");

        input.clear();
        if stdin.read_line(&mut input).expect("failed to read input") == 0 {
            println!();
            break;
        }

        // Check if the query is exit.
        let query = input.strip_suffix('.').unwrap_or(&input).trim();
        if query.eq_ignore_ascii_case("exit") {
            break;
        }

        // Check if the query starts with ~ for fuzzy execution.
        let (is_fuzzy, query) = match query.strip_prefix('~') {
            Some(rest) => (true, rest.trim()),
            None => (false, query),
        };

        // Execute the query
        let solutions = if is_fuzzy {
            program.fuzzy_query(query, 0.01)
        } else {
            program.crisp_query(query)
        };

        // Handle errors
        let solutions = match solutions {
            Ok(solutions) => solutions,
            Err(err) => {
                eprintln!("{err}");
                continue;
            }
        };

        // Print solutions
        if solutions.is_empty() {
            println!("false.");
            continue;
        }

        for (index, solution) in solutions.iter().enumerate() {
            if index > 0 {
                println!();
            }

            // Render each binding in the solution
            let bindings = solution.bindings();
            if bindings.is_empty() {
                print!("true");
            } else {
                // Because Variable and Value implement Display, we can render them directly
                let rendered_bindings = bindings
                    .iter()
                    .map(|(variable, value)| format!("{} = {}", variable, value))
                    .collect::<Vec<_>>()
                    .join(", ");

                print!("{}", rendered_bindings);
            }

            if is_fuzzy {
                print!(", truth = {:.3}", solution.truth_value());
            }

            println!(".");
        }
    }

    Ok(())
}
