use std::fmt::Display;

#[derive(Default)]
pub struct Lexer<'src> {
    errors: Vec<Symbol<Error>>,
    tokens: Vec<Symbol<Token<'src>>>,
}

impl<'src> Lexer<'src> {
    pub fn errors(&self) -> &[Symbol<Error>] {
        &self.errors
    }

    pub fn tokens(&self) -> &[Symbol<Token>] {
        &self.tokens
    }

    pub fn new() -> Self {
        Default::default()
    }

    pub fn lex(&mut self, src: &'src str) {
        let mut line = 0;
        let mut chars = src.char_indices().peekable();
        let mut next = chars.next();

        while let Some((pos, c)) = next {
            if c == '\n' {
                line += 1;
                next = chars.next();
                continue;
            }

            macro_rules! add_error {
                ($inner: expr) => {
                    self.errors.push(Symbol {
                        line,
                        inner: $inner,
                    })
                };
            }

            let next_token = match c {
                '\n' => {
                    line += 1;
                    None
                }
                '(' => Some(Token::LeftParen),
                ')' => Some(Token::RightParen),
                '{' => Some(Token::LeftBrace),
                '}' => Some(Token::RightBrace),
                '-' => Some(Token::Minus),
                '+' => Some(Token::Plus),
                '/' => {
                    if let Some((_, '/')) = chars.peek() {
                        chars.find(|(_, c)| c == &'\n');
                        line += 1;
                        None
                    } else {
                        Some(Token::Slash)
                    }
                }
                '*' => Some(Token::Star),
                ',' => Some(Token::Comma),
                '.' => Some(Token::Dot),
                ';' => Some(Token::Semicolon),
                '=' => Some(if let Some((_, '=')) = chars.peek() {
                    chars.next().unwrap();
                    Token::EqualEqual
                } else {
                    Token::Equal
                }),
                '!' => Some(if let Some((_, '=')) = chars.peek() {
                    chars.next().unwrap();
                    Token::BangEqual
                } else {
                    Token::Bang
                }),
                '<' => Some(if let Some((_, '=')) = chars.peek() {
                    chars.next().unwrap();
                    Token::LessEqual
                } else {
                    Token::Less
                }),
                '>' => Some(if let Some((_, '=')) = chars.peek() {
                    chars.next().unwrap();
                    Token::GreaterEqual
                } else {
                    Token::Greater
                }),
                '"' => {
                    let start_idx = pos + 1;
                    let mut end_idx = start_idx;
                    loop {
                        match chars.next() {
                            Some((_, '"')) => {
                                break Some(Token::String(&src[start_idx..end_idx]));
                            }
                            Some((_, c)) => {
                                if c == '\n' {
                                    line += 1;
                                }

                                end_idx += 1;
                            }
                            None => {
                                add_error!(Error::UnterminatedString);
                                break None;
                            }
                        }
                    }
                }
                '0'..='9' => {
                    let start_idx = pos;
                    let mut end_idx = start_idx + 1;
                    let mut matched_decimal_point = false;

                    loop {
                        let c = chars.peek();
                        match (matched_decimal_point, c) {
                            (false, Some((_, '0'..='9' | '.'))) | (true, Some((_, '0'..='9'))) => {
                                let next = chars.next().unwrap();
                                if next.1 == '.' {
                                    matched_decimal_point = true;
                                }
                                end_idx += 1;
                            }
                            (true, Some((_, '.'))) => {
                                add_error!(Error::UnexpectedCharacter(c.unwrap().1));
                                chars.next().unwrap();
                                break None;
                            }
                            _ => {
                                let float_str_repr = &src[start_idx..end_idx];
                                let float = float_str_repr.parse().unwrap();
                                break Some(Token::Number(float, float_str_repr));
                            }
                        }
                    }
                }
                '_' | 'a'..='z' | 'A'..='Z' => {
                    let start_idx = pos;
                    let mut end_idx = start_idx + 1;
                    while let Some((_, '_' | 'a'..='z' | 'A'..='Z' | '0'..='9')) = chars.peek() {
                        chars.next().unwrap();
                        end_idx += 1;
                    }

                    Some(Token::Identifier(&src[start_idx..end_idx]))
                }
                c if c.is_whitespace() => None,
                invalid => {
                    add_error!(Error::UnexpectedCharacter(invalid));
                    None
                }
            };

            if let Some(next_token) = next_token {
                self.tokens.push(Symbol::new(line, next_token));
            }

            next = chars.next();
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Error {
    UnexpectedCharacter(char),
    UnterminatedString,
}

#[derive(Debug, PartialEq)]
pub struct Symbol<T> {
    line: usize,
    inner: T,
}

impl<T> Symbol<T> {
    pub fn new(line: usize, inner: T) -> Self {
        Self { line, inner }
    }
}

impl Display for Symbol<Token<'_>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner.fmt(f)
    }
}

impl Display for Symbol<Error> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let differing_part = match self.inner {
            Error::UnexpectedCharacter(c) => {
                format!("Unexpected character: {}", c)
            }
            Error::UnterminatedString => String::from("Unterminated string."),
        };

        f.write_fmt(format_args!(
            "[line {}] Error: {differing_part}",
            self.line + 1
        ))
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Token<'src> {
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Minus,
    Plus,
    Slash,
    Star,
    Comma,
    Dot,
    Semicolon,
    Equal,
    EqualEqual,
    Bang,
    BangEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    String(&'src str),
    Number(f64, &'src str),
    Identifier(&'src str),
}

impl<'src> Token<'src> {
    fn literal(&self) -> String {
        if let Self::Number(n, _) = self {
            return if n.fract() == 0.0 {
                format!("{n}.0")
            } else {
                format!("{n}")
            };
        }

        match self {
            Self::String(lit) => lit,
            _ => "null",
        }
        .to_string()
    }
    fn lexeme(&self) -> String {
        if let Self::String(s) = self {
            return format!("\"{s}\"");
        }

        match self {
            Self::LeftParen => "(",
            Self::RightParen => ")",
            Self::LeftBrace => "{",
            Self::RightBrace => "}",
            Self::Minus => "-",
            Self::Plus => "+",
            Self::Slash => "/",
            Self::Star => "*",
            Self::Comma => ",",
            Self::Dot => ".",
            Self::Semicolon => ";",
            Self::Equal => "=",
            Self::EqualEqual => "==",
            Self::Bang => "!",
            Self::BangEqual => "!=",
            Self::Less => "<",
            Self::LessEqual => "<=",
            Self::Greater => ">",
            Self::GreaterEqual => ">=",
            Self::String(..) => unreachable!(),
            Self::Number(_, lit) => lit,
            Self::Identifier(lit) => lit,
        }
        .to_string()
    }
    fn token_type(&self) -> &'static str {
        match self {
            Self::LeftParen => "LEFT_PAREN",
            Self::RightParen => "RIGHT_PAREN",
            Self::LeftBrace => "LEFT_BRACE",
            Self::RightBrace => "RIGHT_BRACE",
            Self::Minus => "MINUS",
            Self::Plus => "PLUS",
            Self::Slash => "SLASH",
            Self::Star => "STAR",
            Self::Comma => "COMMA",
            Self::Dot => "DOT",
            Self::Semicolon => "SEMICOLON",
            Self::Equal => "EQUAL",
            Self::EqualEqual => "EQUAL_EQUAL",
            Self::Bang => "BANG",
            Self::BangEqual => "BANG_EQUAL",
            Self::Less => "LESS",
            Self::LessEqual => "LESS_EQUAL",
            Self::Greater => "GREATER",
            Self::GreaterEqual => "GREATER_EQUAL",
            Self::String(..) => "STRING",
            Self::Number(..) => "NUMBER",
            Self::Identifier(..) => "IDENTIFIER",
        }
    }
}

impl Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{} {} {}",
            self.token_type(),
            self.lexeme(),
            self.literal()
        ))
    }
}
