set shell := ["powershell.exe", "-c"]

alias r := run
alias c := check

run:
	cargo run

check:
	cargo check
	cargo fmt --check
	cargo clippy --all-targets --all-features -- -D warnings
	cargo test

make-pdfs:
	typst c report/main.typ "Final Report.pdf"
	typst c report/logbook.typ "Logbook.pdf"
	typst c report/poster.typ "Poster.pdf"
