RUSTFLAGS=-Zinstrument-coverage LLVM_PROFILE_FILE=./.coverage/coverage-%p-%m.profraw cargo +nightly test

grcov . --binary-path ./target/debug/ -s . -t html --ignore-not-existing --ignore "*cargo*" -o ./.coverage/
xdg-open ./.coverage/src/index.html

#grcov . --binary-path ./target/debug/ -s . -t lcov --ignore-not-existing --ignore "*cargo*" -o ./.coverage/coverage.lcov
#lcov --summary ./.coverage/coverage.lcov
