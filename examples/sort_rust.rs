//! Program to demonstrate using the engine to execute Prolog queries, using a quicksort implementation as an example.

use std::fs;

fn main() {
    let list = (0..15).rev().collect::<Vec<_>>();

    // The query and program could also be constructed using macros, but using strings is easier in this example.
    let program_source =
        fs::read_to_string("examples/quicksort.pl").expect("failed to read program file");
    let program = mimir::Program::new(&program_source).expect("failed to create program");

    println!("Input: {list:?}");

    let query = format!("quicksort({list:?}, X)");
    let solutions = program.crisp_query(&query).expect("query should execute");
    let output_list = first_solution_as_list(&solutions, "X").expect("should have a solution");
    println!("Output: {output_list:?}");

    let query = format!("reverse({list:?}, Y)");
    let solutions = program.crisp_query(&query).expect("query should execute");
    let output_list = first_solution_as_list(&solutions, "Y").expect("should have a solution");
    println!("Reversed: {output_list:?}");
}

fn first_solution_as_list(solutions: &[mimir::Solution], variable: &str) -> Option<Vec<i64>> {
    let solution = solutions.first()?;

    let value = solution
        .get(variable)
        .expect("solution should have the requested variable")
        .clone();

    mimir::flatten_list(&value)
        .expect("could not flatten list")
        .iter()
        .map(|v| {
            v.get_number()
                .expect("list items should be numbers")
                .into_inner() as i64
        })
        .collect::<Vec<_>>()
        .into()
}
