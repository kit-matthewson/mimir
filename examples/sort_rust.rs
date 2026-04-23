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
    let output_list: Vec<f64> = solutions
        .first()
        .expect("should have a solution")
        .get("X")
        .expect("solution should have variable X")
        .try_into()
        .expect("X should be a list");
    println!("Output: {output_list:?}");

    let query = format!("reverse({list:?}, Y)");
    let solutions = program.crisp_query(&query).expect("query should execute");
    let output_list: Vec<f64> = solutions
        .first()
        .expect("should have a solution")
        .get("Y")
        .expect("solution should have variable Y")
        .try_into()
        .expect("Y should be a list");
    println!("Reversed: {output_list:?}");
}
