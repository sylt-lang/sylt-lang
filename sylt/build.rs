use std::path::Path;

fn find_test_paths(directory: &Path) {
    if let Ok(entries) = std::fs::read_dir(directory) {
        println!("cargo:rerun-if-changed={}", directory.display());
        for entry in entries {
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
}

fn main() {
    find_test_paths(Path::new("../tests/"));
}
