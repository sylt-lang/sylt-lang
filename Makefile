.PHONY: b t r build test run

r: run
t: test
b: build

run: build
	cargo run -- a.src

test: build
	cargo test --quiet

build:
	cargo build 
