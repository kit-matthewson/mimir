//! Program to evaluate the performance of the engine.

use std::fs;
use std::io::Write;

fn main() {
    // This program defines reverse/2 and fib/2
    let source = fs::read_to_string("examples/computational_tasks.pl").unwrap();
    let program = mimir::Program::new(&source).unwrap();

    let mut reverse_times = Vec::new();
    for n in (500..1010).step_by(10) {
        let list = (0..n).collect::<Vec<_>>();
        let query = format!("reverse({list:?}, Y)");
        println!("Running query: {query}");
        let start = std::time::Instant::now();
        let _ = program.crisp_query(&query).unwrap();
        let duration = start.elapsed();
        println!("reverse({n} items) time: {duration:?}");
        reverse_times.push((n, duration.as_millis()));

        if duration.as_secs() > 10 {
            println!("reverse({n} items) took too long, stopping further tests");
            break;
        }
    }

    // Vec of (n, time)
    let mut fib_times = Vec::new();
    for n in 0..20 {
        let query = format!("fib({n}, X)");
        let start = std::time::Instant::now();
        let solutions = program.crisp_query(&query).unwrap();
        let fib_n = solutions[0]
            .get("X")
            .unwrap()
            .get_number()
            .unwrap()
            .into_inner();
        let duration = start.elapsed();
        println!("fib({n}) = {fib_n}, time: {duration:?}");
        fib_times.push((n, duration.as_millis()));

        if duration.as_secs() > 10 {
            println!("fib({n}) took too long, stopping further tests");
            break;
        }
    }

    // Write fib_times to a CSV file
    let mut file = std::fs::File::create("fib_times.csv").unwrap();
    writeln!(file, "n,time_ms").unwrap();
    for (n, time) in fib_times {
        writeln!(file, "{n},{time:?}").unwrap();
    }

    // Write reverse_times to a CSV file
    let mut file = std::fs::File::create("reverse_times.csv").unwrap();
    writeln!(file, "n,time_ms").unwrap();
    for (n, time) in reverse_times {
        writeln!(file, "{n},{time:?}").unwrap();
    }
}
