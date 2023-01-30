.PHONY: b t r build test run

r: run
t: test
b: build

run: build
	cargo run -- a.src

test: build
	@cargo test --quiet
	@echo $(shell echo "Ran `find tests -type f | wc -l` golden tests")

build:
	cargo build 
