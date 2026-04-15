use std::{
    env, fs,
    io::{self, Write},
};

fn main() -> Result<(), mimir::MimirError> {
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
        print!("?- ");
        io::stdout().flush().expect("failed to flush stdout");

        input.clear();
        if stdin.read_line(&mut input).expect("failed to read input") == 0 {
            println!();
            break;
        }

        let query = input.strip_suffix('.').unwrap_or(&input).trim();
        if query.eq_ignore_ascii_case("exit") {
            break;
        }

        let (is_fuzzy, query) = match query.strip_prefix('~') {
            Some(rest) => (true, rest.trim()),
            None => (false, query),
        };

        let solutions = if is_fuzzy {
            program.fuzzy_query(query, 0.01)
        } else {
            program.crisp_query(query)
        };

        let solutions = match solutions {
            Ok(solutions) => solutions,
            Err(err) => {
                eprintln!("{err}");
                continue;
            }
        };

        if solutions.is_empty() {
            println!("false.");
            continue;
        }

        for (index, solution) in solutions.iter().enumerate() {
            if index > 0 {
                println!();
            }

            let bindings = solution.bindings();
            if bindings.is_empty() {
                print!("true");
            } else {
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
