set shell := ["powershell.exe", "-c"]

alias r := run
alias c := check

run:
	cargo run

check:
	cargo check
	cargo fmt --check
	cargo clippy
	cargo test

make-pdf:
	typst c report/main.typ "Final Report.pdf"
	typst c report/logbook.typ "Logbook.pdf"
