use std::env;
use std::fs;
use std::io::{self, Write};

enum Token {
    LeftParen,
    RightParen,
}

impl Token {
    fn display(&self) -> &'static str {
        match self {
            Self::LeftParen => "LEFT_PAREN",
            Self::RightParen => "RIGHT_PAREN",
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        writeln!(io::stderr(), "Usage: {} tokenize <filename>", args[0]).unwrap();
        return;
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
                let token = match c {
                    '(' => Token::LeftParen,
                    ')' => Token::RightParen,
                    _ => panic!("Unknown token '{c}'")
                };

                tokens.push(token);
            }

            for t in tokens {
                println!("{} null", t.display());
            }

            println!("EOF  null");
        }
        _ => {
            writeln!(io::stderr(), "Unknown command: {}", command).unwrap();
            return;
        }
    }
}
