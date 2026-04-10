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

gt_ten(X) :-
    X > 10.

is_ten(X) :-
    X = 10.

is_five_or_ten(X) :~
    X = 5,
    0.2.
is_five_or_ten(X) :~
    X = 10,
    0.8.
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

            println!("  {:.2}", solution.truth_value());
        }

        if solutions.is_empty() {
            println!("  false");
        }
    }
}
