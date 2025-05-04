use std::env;
use std::fs;
use std::io::{self, Write};

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
        impl TryFrom<char> for Token {
            type Error = String;
            fn try_from(value: char) -> Result<Self, Self::Error> {
                let token = match value {
                    $($c => $i,)*
                    invalid => return Err(format!("Invalid token '{invalid}'")),
                };

                Ok(token)
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

impl_conversions!{
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
        return Ok(())
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

            let mut tokens = Vec::new();

            for c in file_contents.chars() {
                tokens.push(TryInto::<Token>::try_into(c)?);
            }

            for t in tokens {
                println!("{} {} null", t.display(), Into::<char>::into(&t));
            }

            println!("EOF  null");
        }
        _ => {
            writeln!(io::stderr(), "Unknown command: {}", command).unwrap();
        }
    }

    Ok(())
}
