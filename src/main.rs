use std::env;
use std::fmt::Display;
use std::fs;
use std::io::{self, Write};

struct Symbol {
    line: usize,
    kind: SymbolKind,
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            SymbolKind::Token(t) => f.write_fmt(format_args!(
                "{} {} null",
                t.display(),
                Into::<char>::into(&t)
            )),
            SymbolKind::Error(c) => f.write_fmt(format_args!(
                "[line {}] Error: Unexpected character: {c}",
                self.line + 1
            )),
        }
    }
}

enum SymbolKind {
    Token(Token),
    Error(char),
}
impl SymbolKind {
    fn is_err(&self) -> bool {
        match self {
            Self::Error(..) => true,
            Self::Token(..) => false,
        }
    }
}

#[derive(Clone, Copy)]
enum Token {
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
}

macro_rules! impl_conversions {
    ($($i:path=$c:literal,)*) => {
        impl From<char> for SymbolKind {
            fn from(value: char) -> Self {
                match value {
                    $($c => Self::Token($i),)*
                    invalid => Self::Error(invalid),
                }
            }
        }

        impl Into<char> for &Token {
            fn into(self) -> char {
                match self {
                    $($i => $c,)*
                }
            }
        }
    };
}

impl_conversions! {
    Token::LeftParen='(',
    Token::RightParen=')',

    Token::LeftBrace='{',
    Token::RightBrace='}',

    Token::Minus='-',
    Token::Plus='+',
    Token::Slash='/',
    Token::Star='*',

    Token::Comma=',',
    Token::Dot='.',
    Token::Semicolon=';',
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
        }
    }
}

fn main() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        writeln!(io::stderr(), "Usage: {} tokenize <filename>", args[0]).unwrap();
        return Ok(());
    }

    let command = &args[1];
    let filename = &args[2];

    match command.as_str() {
        "tokenize" => {
            // You can use print statements as follows for debugging, they'll be visible when running tests.
            writeln!(io::stderr(), "Logs from your program will appear here!").unwrap();

            let file_contents = fs::read_to_string(filename).unwrap_or_else(|_| {
                writeln!(io::stderr(), "Failed to read file {}", filename).unwrap();
                String::new()
            });

            let mut symbols = Vec::new();

            for (line, line_contents) in file_contents.lines().into_iter().enumerate() {
                for c in line_contents.chars() {
                    symbols.push(Symbol {
                        line,
                        kind: c.into(),
                    })
                }
            }

            for err in symbols.iter().filter(|s| s.kind.is_err()) {
                println!("{err}")
            }

            for token in symbols.iter().filter(|s| !s.kind.is_err()) {
                println!("{token}")
            }

            println!("EOF  null");
        }
        _ => {
            writeln!(io::stderr(), "Unknown command: {}", command).unwrap();
        }
    }

    Ok(())
}
