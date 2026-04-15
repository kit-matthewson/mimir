set shell := ["powershell.exe", "-c"]

alias r := run
alias c := check

run:
	cargo run

check:
	cargo check
	cargo fmt --check
	cargo clippy --all-targets --all-features -- -D warnings
	cargo test -q

coverage-html:
	cargo +nightly llvm-cov clean --workspace
	cargo +nightly llvm-cov --workspace --all-features --lib --tests --html --output-dir target/llvm-cov

typst mode="c" output="Final Report":
	typst {{mode}} report/main.typ "{{output}}.pdf"
