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
