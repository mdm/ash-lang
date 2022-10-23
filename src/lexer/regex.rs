use std::{str::FromStr, fmt::Display};

use thiserror::Error;

#[derive(Error, Debug)]
enum RegexError {
    #[error("unexpected end of string")]
    UnexpectedEnd,
    #[error("unexpected character at position {0}")]
    UnexpectedCharacter(usize),
}

#[derive(Debug)]
enum CharacterClass {
    Any,
    Singleton(char),
}

impl CharacterClass {
    fn parse(s: &str) -> Result<(Self, usize), RegexError> {    
        todo!()
    }
}

impl Display for CharacterClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CharacterClass::Any => write!(f, "."),
            CharacterClass::Singleton(char) => match char {
                '(' | ')' | '|' | '?' | '*' | '+' | '.' | '\\' => write!(f, "\\{char}"),
                _ => write!(f, "{char}"),
            }
        }
    }
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
    fn parse(s: &str, start: usize) -> Result<(Self, usize), RegexError> {
        if s.len() < start {
            return Err(RegexError::UnexpectedEnd)
        }

        let mut char_indices = s[start..].char_indices().peekable(); // TODO: avoid peeking by skipping at start of parse()

        let mut parsed = match char_indices.next() {
            Some((i, char)) => {
                match char {
                    '(' => {
                        match char_indices.peek() {
                            Some((j, _next)) => {
                                let (parse_result, next_pos) = Regex::parse(s, start + *j)?;
                                char_indices = s[next_pos..].char_indices().peekable();
                                if char_indices.next().is_none() {
                                    return Err(RegexError::UnexpectedEnd)
                                }
                                Self::Group(Box::new(parse_result))
                            }
                            None => return Err(RegexError::UnexpectedEnd),
                        }
                    }
                    ')' | '|' | '?' | '*' | '+' | ']' => {
                        return Err(RegexError::UnexpectedCharacter(start + i));
                    }
                    '\\' => {
                        match char_indices.next() {
                            Some((_j, char)) => Self::Character(CharacterClass::Singleton(char)),
                            None => return Err(RegexError::UnexpectedEnd),
                        }
                    }
                    '.' => Self::Character(CharacterClass::Any),
                    '[' => {
                        todo!() // parse character class
                    }
                    _ => Self::Character(CharacterClass::Singleton(char)),
                }
            }
            None => {
                return Err(RegexError::UnexpectedEnd);
            }
        };

        while let Some((i, char)) = char_indices.next() {
            match char {
                '(' => {
                    match char_indices.peek() {
                        Some((j, _next)) => {
                            let (parse_result, next_pos) = Regex::parse(s, start + *j)?;
                            char_indices = s[next_pos..].char_indices().peekable();
                            if char_indices.next().is_none() {
                                return Err(RegexError::UnexpectedEnd)
                            }
                            parsed = Self::Concat(Box::new(parsed), Box::new(Self::Group(Box::new(parse_result))));
                        }
                        None => return Err(RegexError::UnexpectedEnd),
                    }
                }
                ')' => {
                    if start == 0 {
                        dbg!(&parsed);
                        return Err(RegexError::UnexpectedCharacter(start + i));
                    } else {
                        return Ok((parsed, start + i));
                    }
                },
                '|' => {
                    match char_indices.peek() {
                        Some((j, _next)) => {
                            let (parse_result, next_pos) = Regex::parse(s, start + *j)?;
                            char_indices = s[next_pos..].char_indices().peekable();
                            parsed = Self::Alternative(Box::new(parsed), Box::new(parse_result));
                            if let Some((_k, ')')) = char_indices.next() {
                                return Ok((parsed, next_pos));
                            }
                        }
                        None => return Err(RegexError::UnexpectedEnd),
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
                '\\' => {
                    match char_indices.next() {
                        Some((_j, char)) => {
                            parsed = Self::Concat(Box::new(parsed), Box::new(Self::Character(CharacterClass::Singleton(char))));
                        }
                        None => return Err(RegexError::UnexpectedEnd),
                    }
                }
                '.' => {
                    parsed = Self::Concat(Box::new(parsed), Box::new(Self::Character(CharacterClass::Any)));
                }
                '[' => {
                    todo!() // parse character class
                }
                _ => {
                    parsed = Self::Concat(Box::new(parsed), Box::new(Self::Character(CharacterClass::Singleton(char))));
                }
            }
        }

        Ok((parsed, s.len()))
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

impl Display for Regex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Character(character_class) => write!(f, "{character_class}"),
            Self::Alternative(a, b) => write!(f, "{a}|{b}"),
            Self::Concat(a, b) => write!(f, "{a}{b}"),
            Self::ZeroOrOne(r) => write!(f, "{r}?"),
            Self::ZeroOrMany(r) => write!(f, "{r}*"),
            Self::OneOrMany(r) => write!(f, "{r}+"),
            Self::Group(r) => write!(f, "({r})"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn long_alternative() {
        let repr = "aa|bb";
        let regex = repr.parse::<Regex>().unwrap();
        dbg!(&regex);
        assert_eq!(format!("{regex}"), repr);
    }

    #[test]
    fn chained_alternative() {
        let repr = "a|b|c";
        let regex = repr.parse::<Regex>().unwrap();
        dbg!(&regex);
        assert_eq!(format!("{regex}"), repr);
    }

    #[test]
    fn nested_alternative1() {
        let repr = "a(a|b)b";
        let regex = repr.parse::<Regex>().unwrap();
        dbg!(&regex);
        assert_eq!(format!("{regex}"), repr);
    }

    #[test]
    fn nested_alternative2() {
        let repr = "(a|b)";
        let regex = repr.parse::<Regex>().unwrap();
        dbg!(&regex);
        assert_eq!(format!("{regex}"), repr);
    }

    #[test]
    fn repetition_precedence() {
        let repr = "a|b|c*";
        let regex = repr.parse::<Regex>().unwrap();
        dbg!(&regex);
        assert_eq!(format!("{regex}"), repr);
    }

    #[test]
    fn group_precedence() {
        let repr = "(a|b|c)*";
        let regex = repr.parse::<Regex>().unwrap();
        dbg!(&regex);
        assert_eq!(format!("{regex}"), repr);
    }

    #[test]
    fn escaped_alternative() {
        let repr = "a\\|b";
        let regex = repr.parse::<Regex>().unwrap();
        dbg!(&regex);
        assert_eq!(format!("{regex}"), repr);
    }

    #[test]
    fn trailing_backslash() {
        let repr = "a\\";
        let result = repr.parse::<Regex>();
        dbg!(&result);
        assert!(matches!(result, Err(RegexError::UnexpectedEnd)));
    }

    #[test]
    fn missing_closing_parenthesis() {
        let repr = "a|(b";
        let result = repr.parse::<Regex>();
        dbg!(&result);
        assert!(matches!(result, Err(RegexError::UnexpectedEnd)));
    }

    #[test]
    fn unexpected_opening_parenthesis1() {
        let repr = "a|)b";
        let result = repr.parse::<Regex>();
        dbg!(&result);
        assert!(matches!(result, Err(RegexError::UnexpectedCharacter(2))));
    }

    #[test]
    fn unexpected_opening_parenthesis2() {
        let repr = "a)b";
        let result = repr.parse::<Regex>();
        dbg!(&result);
        assert!(matches!(result, Err(RegexError::UnexpectedCharacter(1))));
    }
}
