use std::fmt;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use sylt_common::error::Error;

#[derive(Debug, Clone)]
pub enum TestableError {
    Type(String),
    Runtime,
    Syntax(Option<usize>),
    Containing(String),
}

#[derive(Debug, Clone)]
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
            TestableError::Type(msg) => write!(f, "TypeError - containing {:?}", msg),
            TestableError::Runtime => write!(f, "RuntimeError"),
            TestableError::Syntax(Some(line)) => write!(f, "SyntaxError - on line {}", line),
            TestableError::Syntax(None) => write!(f, "SyntaxError - somewhere"),
            TestableError::Containing(line) => write!(f, "Error containing - {:?}", line),
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
            (Error::SyntaxError { span, .. }, TestableError::Syntax(Some(line))) => {
                span.line_start == *line
            }
            (Error::SyntaxError { .. }, TestableError::Syntax(None)) => true,
            (Error::RuntimeError, TestableError::Runtime) => true,
            (Error::TypeError { .. }, TestableError::Type(msg)) => {
                format!("{:?}", a).contains(msg) || format!("{}", a).contains(msg)
            }
            (_, TestableError::Containing(msg)) => {
                format!("{:?}", a).contains(msg) || format!("{}", a).contains(msg)
            }
            _ => false,
        })
}

pub fn write_errors(result: &[Error], expected: &[TestableError]) {
    eprintln!("* GOT {} ERRORS", result.len());
    for err in result.iter() {
        eprintln!("  {}", err);
    }

    eprintln!("* EXPECTED {} ERRORS", expected.len());
    for err in expected.iter() {
        eprintln!("  {}", err);
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
                Some("@") => TestableError::Syntax(usize::from_str(&line[1..]).ok()),
                _ => TestableError::Containing(line.trim().into()),
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
    for entry in
        std::fs::read_dir(directory).expect(&format!("There is no such directory: {:?}", directory))
    {
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
            tests.push(TestSettings { path, ..settings });
        }
    }
    tests
}

fn run_test<R>(reader: R, settings: &TestSettings) -> bool
where
    R: Fn(&Path) -> Result<String, Error>,
{
    use std::process::{Command, Stdio};

    let mut args = crate::Args::default();
    args.args = vec![settings.path.to_str().unwrap().to_string()];
    args.verbosity = if settings.print { 1 } else { 0 };

    let mut child = Command::new("lua")
        .stdin(Stdio::piped())
        .stderr(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect(&format!("Failed to start: {:?}", settings.path));

    let mut stdin = child.stdin.take().unwrap();
    let res = crate::compile_with_reader_to_writer(&args, reader, &mut stdin);

    drop(stdin); // Close stdin so the child can do its thing.

    if let Err(errs) = res.clone() {
        if compare_errors(errs.as_slice(), settings.errors.as_slice()) {
            return true;
        }
        eprintln!("\n=== {:?} - failed in compiler", settings.path);
        write_errors(&errs, &settings.errors);
        return false;
    }

    let output = child.wait_with_output().unwrap();
    // HACK(ed): Status is always 0 when piping to STDIN, atleast on my version of lua,
    // so we check stderr - which is a bad idea.
    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let errs = if !(output.status.success() && stderr.is_empty()) {
        vec![Error::RuntimeError]
    } else {
        Vec::new()
    };

    if !compare_errors(errs.as_slice(), settings.errors.as_slice()) {
        eprintln!("\n=== {:?} - failed in runtime", settings.path);
        if !stdout.is_empty() {
            eprintln!("= STDOUT =\n{}", stdout);
        }
        if !stderr.is_empty() {
            eprintln!("= STDERR =\n{}", stderr);
        }
        write_errors(&errs, &settings.errors);
        return false;
    }

    true
}

#[test]
fn program_tests() {
    use crate::{formatter::format, read_file};
    use std::env::set_current_dir;
    use std::io::Write;
    set_current_dir("../").unwrap();
    let tests = find_and_parse_tests(Path::new("tests/"));
    let mut failed = Vec::new();

    writeln!(
        std::io::stdout().lock(),
        "= RUNNING {} TESTS =",
        tests.len()
    )
    .unwrap();

    for test in tests.iter() {
        if !run_test(read_file, test) {
            failed.push(test);
            continue;
        }

        if test.errors.is_empty()
            && !run_test(
                |path| {
                    format(path).map_err(|errs| panic!("Got errors from formatter!:\n{:?}", errs))
                },
                test,
            )
        {
            failed.push(test);
            continue;
        }
    }
    // TODO(ed): Add time
    // Maybe even time/test?
    // How much overview do we want?
    if !failed.is_empty() {
        eprintln!("\nFailed tests:");
        for fail in failed.iter() {
            eprintln!(" {}", fail.path.to_str().unwrap());
        }
    }

    let num_tests = tests.len();
    let num_failed = failed.len();
    let num_passed = tests.len() - failed.len();
    eprintln!(
        "\n SUMMARY {}/{}      {} failed\n",
        num_passed, num_tests, num_failed
    );
    assert!(failed.is_empty(), "Some tests failed!");
}
