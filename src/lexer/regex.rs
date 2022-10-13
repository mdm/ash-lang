use std::{str::FromStr, fmt::Display};

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
    Singleton(char),
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
                    '\\' => {
                        match char_indices.next() {
                            Some((_j, char)) => Self::Character(CharacterClass::Singleton(char)),
                            None => return Err(RegexError::Empty),
                        }
                    }
                    '.' => Self::Character(CharacterClass::Any),
                    _ => Self::Character(CharacterClass::Singleton(char)),
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
                '\\' => {
                    match char_indices.next() {
                        Some((_j, char)) => {
                            parsed = Self::Concat(Box::new(parsed), Box::new(Self::Character(CharacterClass::Singleton(char))));
                        }
                        None => return Err(RegexError::Empty),
                    }
                }
                '.' => {
                    parsed = Self::Concat(Box::new(parsed), Box::new(Self::Character(CharacterClass::Any)));
                }
                _ => {
                    parsed = Self::Concat(Box::new(parsed), Box::new(Self::Character(CharacterClass::Singleton(char))));
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
    fn nested_alternative() {
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

}
