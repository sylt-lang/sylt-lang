use crate::tokenizer::{PlacedToken, Token, file_to_tokens};

use std::collections::HashSet;
use std::path::{Path, PathBuf};

pub struct Section {
    pub tokens: Vec<PlacedToken>,
    pub path: PathBuf,
}

impl Section {
    fn new(path: PathBuf, tokens: &[PlacedToken]) -> Self {
        Self {
            tokens: Vec::from(tokens),
            path,
        }
    }
}

pub fn sectionize(path: &Path) -> Vec<Section> {
    let mut read_files = HashSet::new();
    read_files.insert(path.to_path_buf());
    let tokens = file_to_tokens(path);
    let mut all_tokens = vec![(path.to_path_buf(), tokens)];
    let mut sections = Vec::new();

    let mut i = 0;
    while i < all_tokens.len() {
        let (path, tokens) = all_tokens[i].clone();
        i += 1;
        let mut last = 0;
        let mut curr = 0;
        while curr < tokens.len() {
            if match (tokens.get(curr + 0), tokens.get(curr + 1), tokens.get(curr + 2)) {
                (Some((Token::Newline, _)), ..)
                    => {
                        if curr == last {
                            last += 1;
                        }
                        false
                    },

                (Some((Token::Use, _)),
                 Some((Token::Identifier(use_file), _)),
                 Some((Token::Newline, _))) => {
                    curr += 3;
                    let use_file: PathBuf = format!("{}.sy", use_file).into();
                    if !read_files.contains(&use_file) {
                        let use_file_tokens = file_to_tokens(&use_file);
                        read_files.insert(use_file.clone());
                        all_tokens.push((use_file, use_file_tokens))
                    }
                    true
                },

                (Some((Token::LeftBrace, _)), ..)
                    => {
                        let mut blocks = 0;
                        loop {
                            curr += 1;
                            match tokens.get(curr) {
                                Some((Token::LeftBrace, _)) => {
                                    blocks += 1;
                                }

                                Some((Token::RightBrace, _)) => {
                                    curr += 1;
                                    blocks -= 1;
                                    if blocks <= 0 {
                                        break;
                                    }
                                }

                                None => {
                                    break;
                                }

                                _ => {}
                            }
                        }
                        false
                    },

                (Some((Token::Identifier(_), _)),
                 Some((Token::ColonColon, _)),
                 Some((Token::Fn, _)))
                    => true,

                (Some((Token::Identifier(_), _)),
                 Some((Token::ColonColon, _)),
                 Some(_))
                    => true,

                (Some((Token::Identifier(_), _)),
                 Some((Token::ColonEqual, _)),
                 Some(_))
                    => true,

                _ => false,
            } {
                sections.push(Section::new(path.clone(), &tokens[last..curr]));
                last = curr;
            }
            curr += 1;
        }
        sections.push(Section::new(path.clone(), &tokens[last..curr]));
    }
    sections
}
