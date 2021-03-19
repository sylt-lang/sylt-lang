use std::path::Path;

fn find_test_paths(directory: &Path) {
    println!("cargo:rerun-if-changed={}", directory.display());
    for entry in std::fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        let file_name = path.file_name().unwrap().to_str().unwrap();

        if file_name.starts_with("_") {
            continue;
        }

        if path.is_dir() {
            find_test_paths(&path);
        }
    }
}

fn main() {
    find_test_paths(Path::new("progs/"));
}
