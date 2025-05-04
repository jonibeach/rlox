use std::fmt::Display;

pub struct Lexer {
    errors: Vec<Symbol<Error>>,
    tokens: Vec<Symbol<Token>>,
    prev_token: Option<Token>,
}

impl Lexer {
    pub fn errors(&self) -> &[Symbol<Error>] {
        &self.errors
    }

    pub fn tokens(&self) -> &[Symbol<Token>] {
        &self.tokens
    }

    pub fn new() -> Self {
        Self {
            errors: Vec::new(),
            tokens: Vec::new(),
            prev_token: None,
        }
    }

    pub fn lex(&mut self, lines: impl IntoIterator<Item = impl AsRef<str>>) {
        'lines: for (line, line_contents) in lines.into_iter().enumerate() {
            macro_rules! unset_prev {
                () => {
                    eprintln!("unsetting prev_token, was {:?}", self.prev_token);
                    self.prev_token = None;
                };
            }
            macro_rules! add_token {
                ($inner:path) => {
                    eprintln!("adding token {:?}", $inner);
                    self.tokens.push(Symbol {
                        line,
                        inner: $inner,
                    });
                };
            }

            macro_rules! add_error {
                ($c:ident) => {
                    self.errors.push(Symbol {
                        line,
                        inner: Error($c),
                    });
                    unset_prev!();
                };
            }

            for c in line_contents.as_ref().chars() {
                eprintln!("next char {c}");
                macro_rules! add_and_unset_prev {
                    ($inner:path) => {
                        add_token!($inner);
                        unset_prev!();
                    };
                }

                match (self.prev_token, c) {
                    (Some(Token::Equal), '=') => {
                        add_and_unset_prev!(Token::EqualEqual);
                        continue;
                    }
                    (Some(Token::Bang), '=') => {
                        add_and_unset_prev!(Token::BangEqual);
                        continue;
                    }
                    (Some(Token::Less), '=') => {
                        add_and_unset_prev!(Token::LessEqual);
                        continue;
                    }
                    (Some(Token::Greater), '=') => {
                        add_and_unset_prev!(Token::GreaterEqual);
                        continue;
                    }
                    // Handle comments by skipping to the next line
                    (Some(Token::Slash), '/') => {
                        unset_prev!();
                        continue 'lines;
                    }
                    (Some(prev), ..) => {
                        add_and_unset_prev!(prev);
                    }
                    (None, ..) => {}
                };

                let new_prev_token = match c {
                    '(' => Token::LeftParen,
                    ')' => Token::RightParen,
                    '{' => Token::LeftBrace,
                    '}' => Token::RightBrace,
                    '-' => Token::Minus,
                    '+' => Token::Plus,
                    '/' => Token::Slash,
                    '*' => Token::Star,
                    ',' => Token::Comma,
                    '.' => Token::Dot,
                    ';' => Token::Semicolon,
                    '=' => Token::Equal,
                    '!' => Token::Bang,
                    '<' => Token::Less,
                    '>' => Token::Greater,
                    c if c.is_whitespace() => {
                        eprintln!("skipping whitespace");
                        unset_prev!();
                        continue;
                    }
                    invalid => {
                        add_error!(invalid);
                        continue;
                    }
                };

                eprintln!("setting prev_token to {:?}", new_prev_token);

                self.prev_token = Some(new_prev_token);
            }

            if let Some(prev) = self.prev_token {
                add_token!(prev);
                unset_prev!();
            }
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Error(char);

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

impl Display for Symbol<Token> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{} {} null",
            self.inner.display(),
            Into::<&str>::into(&self.inner)
        ))
    }
}

impl Display for Symbol<Error> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "[line {}] Error: Unexpected character: {}",
            self.line + 1,
            self.inner.0,
        ))
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Token {
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
}

impl Into<&'static str> for &Token {
    fn into(self) -> &'static str {
        match self {
            Token::LeftParen => "(",
            Token::RightParen => ")",
            Token::LeftBrace => "{",
            Token::RightBrace => "}",
            Token::Minus => "-",
            Token::Plus => "+",
            Token::Slash => "/",
            Token::Star => "*",
            Token::Comma => ",",
            Token::Dot => ".",
            Token::Semicolon => ";",
            Token::Equal => "=",
            Token::EqualEqual => "==",
            Token::Bang => "!",
            Token::BangEqual => "!=",
            Token::Less => "<",
            Token::LessEqual => "<=",
            Token::Greater => ">",
            Token::GreaterEqual => ">=",
        }
    }
}

impl Token {
    fn display(&self) -> &'static str {
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
        }
    }
}
