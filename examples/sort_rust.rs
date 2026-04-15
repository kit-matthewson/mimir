use std::fs;

fn main() {
    let list = (0..20).rev().collect::<Vec<_>>();

    // The query and program could also be constructed using macros, but using strings is easier in this example.
    let program_source =
        fs::read_to_string("examples/quicksort.pl").expect("failed to read program file");
    let program = mimir::Program::new(&program_source).expect("failed to create program");

    println!("Input list: {list:?}");

    let query = format!("quicksort({list:?}, Sorted)");
    println!("Query: {query}");

    let solutions = program.crisp_query(&query).expect("query should execute");
    if let Some(solution) = solutions.first() {
        let value = solution
            .get("Sorted")
            .expect("should have a binding for Sorted")
            .clone();

        let sorted_list = mimir::flatten_list(&value)
            .expect("could not flatten list")
            .iter()
            .map(|v| {
                v.get_number()
                    .expect("list items should be numbers")
                    .into_inner() as i64
            })
            .collect::<Vec<_>>();

        println!("Output list: {sorted_list:?}");
    } else {
        println!("No solutions found.");
    }
}
