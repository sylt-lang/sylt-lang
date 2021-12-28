use std::fmt;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use sylt_common::error::Error;

pub enum TestableError {
    Type(String),
    Runtime,
    Syntax(usize),
}

pub struct TestSettings {
    pub path: PathBuf,
    pub errors: Vec<TestableError>,
    pub print: bool,
}

impl Default for TestSettings {
    fn default() -> Self {
        Self {
            errors: Vec::new(),
            print: true,
            path: PathBuf::new(),
        }
    }
}

impl TestSettings {
    pub fn any_runtime_errors(&self) -> bool {
        self.errors
            .iter()
            .find(|e| matches!(e, TestableError::Runtime))
            .is_some()
    }
}

impl fmt::Display for TestableError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            TestableError::Type(msg) => writeln!(f, "TypeError - containing {:?}", msg),
            TestableError::Runtime => writeln!(f, "RuntimeError"),
            TestableError::Syntax(line) => writeln!(f, "SyntaxError - on line {}", line),
        }
    }
}

pub fn compare_errors(result: &[Error], expected: &[TestableError]) -> bool {
    if result.len() != expected.len() {
        return false;
    }
    result
        .iter()
        .zip(expected.iter())
        .all(|(a, b)| match (a, b) {
            (Error::SyntaxError { span, .. }, TestableError::Syntax(line)) => {
                span.line_start == *line
            }
            (Error::RuntimeError, TestableError::Runtime) => true,
            (Error::TypeError { .. }, TestableError::Type(msg)) => {
                format!("{:?}", a).contains(msg)
            }
            _ => false,
        })
}

pub fn write_errors(
    f: &mut fmt::Formatter<'_>,
    result: &[Error],
    expected: &[TestableError],
) -> fmt::Result {
    writeln!(f, "=== GOT {} ERRORS ===", result.len())?;
    for err in result.iter() {
        writeln!(f, "> {}", err)?;
    }

    writeln!(f, "=== EXPECTED {} ERRORS ===", expected.len())?;
    for err in expected.iter() {
        writeln!(f, "> {}", err)?;
    }

    Ok(())
}

pub fn check_errors(
    f: &mut fmt::Formatter<'_>,
    result: &[Error],
    expected: &[TestableError]) -> fmt::Result {
    if !compare_errors(result, expected) {
        write_errors(f, result, expected)
    } else {
        Ok(())
    }
}

fn parse_test_settings(contents: String) -> TestSettings {
    let mut settings = TestSettings::default();

    let mut errors = Vec::new();
    for line in contents.split("\n") {
        if line.starts_with("// error:") {
            let line = line.strip_prefix("// error:").unwrap().trim().to_string();
            let err = match line.get(0..1) {
                Some("$") => TestableError::Type(line[1..].trim().into()),
                Some("#") => TestableError::Runtime,
                Some("@") => TestableError::Syntax(
                    usize::from_str(&line[1..])
                        .expect("Failed to parse line number for syntax error"),
                ),
                _ => continue,
            };
            errors.push(err);
        } else if line.starts_with("// flags:") {
            for flag in line
                .strip_prefix("// flags:")
                .unwrap()
                .trim()
                .split(" ")
                .skip(2)
            {
                match flag {
                    "no_print" => {
                        settings.print = false;
                    }
                    _ => {
                        panic!("Unknown test flag '{}'", flag);
                    }
                }
            }
        }
    }

    TestSettings { errors, ..settings }
}

fn find_and_parse_tests(directory: &Path) -> Vec<TestSettings> {
    let mut tests = Vec::new();
    for entry in std::fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        let file_name = path.file_name().unwrap().to_str().unwrap();

        if file_name.starts_with("_") {
            continue;
        }

        if path.is_dir() {
            tests.extend(find_and_parse_tests(&path));
        } else {
            if !file_name.ends_with(".sy") {
                continue;
            }
            let settings = parse_test_settings(std::fs::read_to_string(&path).unwrap());
            tests.push(TestSettings { path: path, ..settings });
        }
    }
    tests
}

fn run_test<R>(reader: R, settings: &TestSettings) -> bool
where
    R: Fn(&Path) -> Result<String, Error>,
{
}

#[test]
fn program_tests() {
    let tests = find_and_parse_tests(Path::new("tests/"));
    let mut passed = 0;
    for test in tests.iter() {
        if run_test(crate::read_file, test) {
            passed += 1;
        }
    }
    eprintln!("> {}/{}", passed, tests.len());
}
