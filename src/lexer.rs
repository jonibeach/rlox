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
        for (line, line_contents) in lines.into_iter().enumerate() {
            let mut add_token = |inner: Token| self.tokens.push(Symbol { line, inner });
            let mut add_error = |c: char| {
                self.errors.push(Symbol {
                    line,
                    inner: Error(c),
                })
            };

            for c in line_contents.as_ref().chars() {
                let curr_prev_token = self.prev_token.clone();
                let mut add_and_unset_prev = |inner: Token| {
                    add_token(inner);
                    self.prev_token = None;
                };

                match (curr_prev_token, c) {
                    (Some(Token::Equal), '=') => {
                        add_and_unset_prev(Token::EqualEqual);
                        continue;
                    }
                    (Some(Token::Bang), '=') => {
                        add_and_unset_prev(Token::BangEqual);
                        continue;
                    }
                    (Some(prev), ..) => add_and_unset_prev(prev),
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
                    invalid => {
                        add_error(invalid);
                        continue;
                    }
                };

                self.prev_token = Some(new_prev_token);
            }

            if let Some(prev) = self.prev_token {
                add_token(prev)
            }
        }
    }
}

pub struct Error(char);

pub struct Symbol<T> {
    line: usize,
    inner: T,
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

#[derive(Clone, Copy)]
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
        }
    }
}
