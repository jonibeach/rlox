use std::env;
use std::fs;

use codecrafters_interpreter::lexer::Lexer;

fn main() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: {} tokenize <filename>", args[0]);
        return Ok(());
    }

    let command = &args[1];
    let filename = &args[2];

    match command.as_str() {
        "tokenize" => {
            let file_contents = fs::read_to_string(filename).unwrap_or_else(|_| {
                eprintln!("Failed to read file {}", filename);
                String::new()
            });

            let mut lexer = Lexer::new();

            lexer.lex(&file_contents);

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
        _ => {
            eprintln!("Unknown command: {}", command);
        }
    }

    Ok(())
}
