#[test]
fn test_file_parsing() {
    // Get path to tests/prolog_files
    let manifest_dir =
        std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR should be set by Cargo");
    let test_dir = std::path::Path::new(&manifest_dir)
        .join("tests")
        .join("prolog_files");

    let paths = std::fs::read_dir(&test_dir).unwrap();

    for path in paths {
        let path = path.unwrap().path();

        // Only attempt .pl files
        if path.extension().and_then(|s| s.to_str()) == Some("pl") {
            // Get contents and attempt to parse
            let content = std::fs::read_to_string(&path).unwrap();
            let res = mimir::Program::new(&content, 0.5);

            assert!(
                res.is_ok(),
                "Failed to parse file {:?}: {:?}",
                path,
                res.err()
            );
        }
    }
}
