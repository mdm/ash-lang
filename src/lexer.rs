use std::str::FromStr;

use thiserror::Error;

#[derive(Error, Debug)]
enum RegexError {
    #[error("unexpected end of string")]
    Empty,
    #[error("unknown regex error")]
    Unknown,
}

#[derive(Debug)]
enum CharacterClass {
    Any,
}

#[derive(Debug)]
enum Regex {
    Character(CharacterClass),
    Alternative(Box<Regex>, Box<Regex>), // precedence 1
    Concat(Box<Regex>, Box<Regex>), // precedence 2
    ZeroOrOne(Box<Regex>), // precedence 3
    ZeroOrMany(Box<Regex>), // precedence 3
    OneOrMany(Box<Regex>), // precedence 3
    Group(Box<Regex>),
}

impl Regex {
    fn parse(s: &str, start: usize) -> Result<(Self, &str), RegexError> {
        let mut char_indices = s.char_indices().peekable(); // TODO: avoid peeking by skipping at start of parse()

        let mut parsed = match char_indices.next() {
            Some((_i, char)) => {
                match char {
                    '(' => {
                        match char_indices.peek() {
                            Some((j, _next)) => {
                                let parse_result = Regex::parse(&s[*j..], *j)?;
                                char_indices = parse_result.1.char_indices().peekable();
                                char_indices.next();
                                Self::Group(Box::new(parse_result.0))
                            }
                            None => return Err(RegexError::Empty),
                        }
                    }
                    ')' | '|' | '?' | '*' | '+' => {
                        return Err(RegexError::Unknown); // unexpected char
                    }
                    _ => Self::Character(CharacterClass::Any),
                }
            }
            None => {
                return Err(RegexError::Empty);
            }
        };

        while let Some((i, char)) = char_indices.next() {
            match char {
                '(' => {
                    match char_indices.peek() {
                        Some((j, _next)) => {
                            let parse_result = Regex::parse(&s[*j..], *j)?;
                            char_indices = parse_result.1.char_indices().peekable();
                            char_indices.next();
                            parsed = Self::Concat(Box::new(parsed), Box::new(Self::Group(Box::new(parse_result.0))));
                        }
                        None => return Err(RegexError::Empty),
                    }
                }
                ')' => {
                    if start == 0 {
                        dbg!(&parsed);
                        return Err(RegexError::Unknown); // unexpected char
                    } else {
                        return Ok((parsed, &s[i..]));
                    }
                },
                '|' => {
                    match char_indices.peek() {
                        Some((j, _next)) => {
                            let parse_result = Regex::parse(&s[*j..], *j)?;
                            char_indices = parse_result.1.char_indices().peekable();
                            parsed = Self::Alternative(Box::new(parsed), Box::new(parse_result.0));
                            if let Some((k, ')')) = char_indices.next() {
                                return Ok((parsed, &parse_result.1[k..]));
                            }
                        }
                        None => return Err(RegexError::Empty),
                    }
                },
                '?' => {
                    parsed = parsed.wrap_rightmost(Self::ZeroOrOne);
                }
                '*' => {
                    parsed = parsed.wrap_rightmost(Self::ZeroOrMany);
                }
                '+' => {
                    parsed = parsed.wrap_rightmost(Self::OneOrMany);
                }
                _ => {
                    parsed = Self::Concat(Box::new(parsed), Box::new(Self::Character(CharacterClass::Any)));
                }
            }
        }

        Ok((parsed, ""))
    }

    fn wrap_rightmost(self, wrapping_fn: impl Fn(Box<Self>) -> Self) -> Self {
        match self {
            Self::Alternative(a, b) => Self::Alternative(a, Box::new(b.wrap_rightmost(wrapping_fn))),
            Self::Concat(a, b) => Self::Concat(a, Box::new(b.wrap_rightmost(wrapping_fn))),
            regex => (wrapping_fn)(Box::new(regex)),
        }
    }
}

impl FromStr for Regex {
    type Err = RegexError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Regex::parse(s, 0).map(|(r, _)| r)
    }
}

enum TokenClass {
    Identifier,
    StringLiteral,
    IntegerLiteral,
    FloatLiteral,
    Operator,
    Separator,
    EndOfInput,
}

struct DottedItem {
    token_class: TokenClass,
    dot: usize,
}

struct TransitionTable {
    base: Vec<usize>, // TODO: do we need HasshMaps here if we want to support arbitrary Unicode chars?
    next: Vec<usize>,
    check: Vec<usize>,
    default: Vec<usize>,
}

struct Lexer {
    states: Vec<DottedItem>,
    transitions: TransitionTable,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn long_alternative() {
        let regex = "aa|bb".parse::<Regex>().unwrap();
        dbg!(&regex);
        assert!(matches!(regex, Regex::Alternative(_, _)));
        if let Regex::Alternative(aa, bb) = regex {
            assert!(matches!(*aa, Regex::Concat(_, _)));
            if let Regex::Concat(a1, a2) = *aa {
                assert!(matches!(*a1, Regex::Character(CharacterClass::Any)));
                assert!(matches!(*a2, Regex::Character(CharacterClass::Any)));
            }

            assert!(matches!(*bb, Regex::Concat(_, _)));
            if let Regex::Concat(b1, b2) = *bb {
                assert!(matches!(*b1, Regex::Character(CharacterClass::Any)));
                assert!(matches!(*b2, Regex::Character(CharacterClass::Any)));
            }
        }
    }

    #[test]
    fn chained_alternative() {
        let regex = "a|b|c".parse::<Regex>().unwrap();
        dbg!(&regex);
    }

    #[test]
    fn nested_alternative() {
        let regex = "a(a|b)b".parse::<Regex>().unwrap();
        dbg!(&regex);
    } 

    #[test]
    fn nested_alternative2() {
        let regex = "(a|b)".parse::<Regex>().unwrap();
        dbg!(&regex);
    } 
}