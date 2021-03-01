use std::path::{Path, PathBuf};

fn find_tests(directory: &Path) -> Vec<PathBuf> {
    let mut tests = Vec::new();

    for entry in std::fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();

        if path.file_name().unwrap().to_str().unwrap().starts_with("_") {
            continue;
        }

        if path.is_dir() {
            tests.append(&mut find_tests(&path));
        } else {
            assert!(!path.to_str().unwrap().contains(","), "You should be ashamed.");
            tests.push(path);
        }
    }

    tests
}

fn main() {
    let tests = find_tests(Path::new("progs/"));
    let files = tests.iter().fold(String::new(), |a, b| format!("{},{}", a, b.display()));
    println!("cargo:rustc-env=SCRIPTS={}", &files[1..]);
}
