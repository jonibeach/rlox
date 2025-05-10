use std::env;
use std::fs;

use codecrafters_interpreter::lexer::Lexer;
use codecrafters_interpreter::parser::Parser;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: {} tokenize <filename>", args[0]);
        return;
    }

    let command = &args[1];
    let filename = &args[2];

    let file_contents = fs::read_to_string(filename).unwrap_or_else(|_| {
        eprintln!("Failed to read file {}", filename);
        String::new()
    });

    let mut lexer = Lexer::new();

    lexer.lex(&file_contents);

    match command.as_str() {
        "tokenize" => {
            for err in lexer.errors() {
                eprintln!("{err}")
            }

            for token in lexer.tokens() {
                println!("{token}");
            }

            println!("EOF  null");

            if !lexer.errors().is_empty() {
                std::process::exit(65)
            }
        }
        "parse" => {
            let parser = Parser::new(lexer.tokens());
            let ast = match parser.parse() {
                Ok(ast) => ast,
                Err(..) => std::process::exit(65),
            };
            println!("{ast}");
        }
        "evaluate" => {
            let parser = Parser::new(lexer.tokens());
            let ast = match parser.parse() {
                Ok(ast) => ast,
                Err(..) => std::process::exit(65),
            };
            match ast.eval() {
                Ok(res) => println!("{res}"),
                Err(e) => {
                    eprintln!("{e}");
                    std::process::exit(70)
                }
            }
        }
        _ => {
            eprintln!("Unknown command: {}", command);
        }
    }
}
