.PHONY: b t r o build test run overwrite

r: run
t: test
o: overwrite
b: build

run: build
	cargo run -- a.src

test: build
	@cargo test --quiet
	@echo $(shell echo "Ran `find tests -type f | wc -l` golden tests")

overwrite: build
	OVERWRITE=1 make test

build:
	cargo build 
