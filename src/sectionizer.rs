use std::collections::HashSet;
use std::path::{Path, PathBuf};

use crate::error::Error;
use crate::path_to_module;
use crate::tokenizer::{file_to_tokens, PlacedToken, Token};

#[derive(Debug)]
pub struct Section {
    pub tokens: Vec<PlacedToken>,
    pub path: PathBuf,
    pub faulty: bool,
}

impl Section {
    fn new(path: PathBuf, tokens: &[PlacedToken]) -> Self {
        Self {
            tokens: Vec::from(tokens),
            path,
            faulty: false,
        }
    }
}

pub fn sectionize(path: &Path) -> Result<Vec<Section>, Vec<Error>> {
    let mut read_files = HashSet::new();
    read_files.insert(path.to_path_buf());
    let tokens = file_to_tokens(path).map_err(|_| {
        vec![Error::FileNotFound(path.to_path_buf())]
    })?;
    let mut all_tokens = vec![(path.to_path_buf(), tokens)];
    let mut sections = Vec::new();
    let mut errors = Vec::new();

    let mut i = 0;
    while i < all_tokens.len() {
        let (path, tokens) = all_tokens[i].clone();
        i += 1;
        let mut last = 0;
        let mut curr = 0;
        while curr < tokens.len() {
            if match (
                tokens.get(curr + 0),
                tokens.get(curr + 1),
                tokens.get(curr + 2),
            ) {
                (Some((Token::Newline, _)), ..) => {
                    if curr == last {
                        last += 1;
                    }
                    false
                }

                (
                    Some((Token::Use, _)),
                    Some((Token::Identifier(file), _)),
                    Some((Token::Newline, _line)),
                ) => {
                    let use_file = path_to_module(&path, file);
                    if !read_files.contains(&use_file) {
                        read_files.insert(use_file.clone());
                        match file_to_tokens(&use_file) {
                            Ok(tokens) => all_tokens.push((use_file, tokens)),
                            Err(_) => {
                                // TODO(ed): We discard line and current file
                                // error info here, might be usefull!
                                errors.push(Error::FileNotFound(use_file))
                            }
                        }
                    }
                    true
                }

                (Some((Token::LeftBrace, _)), ..) => {
                    let mut blocks = 0;
                    loop {
                        match tokens.get(curr) {
                            Some((Token::LeftBrace, _)) => { blocks += 1; }
                            Some((Token::RightBrace, _)) => { blocks -= 1; }
                            None => { break; }
                            _ => {}
                        }
                        if blocks == 0 {
                            break;
                        }
                        curr += 1;
                    }
                    false
                }

                (Some((Token::Identifier(_), _)), Some((Token::ColonColon, _)), Some(_)) => true,

                (Some((Token::Identifier(_), _)), Some((Token::ColonEqual, _)), Some(_)) => true,

                _ => false,
            } {
                sections.push(Section::new(path.clone(), &tokens[last..curr]));
                last = curr;
            }
            curr += 1;
        }
        sections.push(Section::new(path.clone(), &tokens[last..curr]));
    }
    if errors.is_empty() {
        Ok(sections)
    } else {
        Err(errors)
    }
}
