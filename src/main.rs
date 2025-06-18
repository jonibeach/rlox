use std::env;
use std::fs;

use rlox::eval::Executor;
use rlox::lexer::Lexer;
use rlox::parser::Parser;

fn main() {
    let args: Vec<String> = env::args().collect();

    let filename = args.get(1).expect("Usage: rlox <filename>");

    let file_contents = fs::read_to_string(filename).unwrap_or_else(|_| {
        eprintln!("Failed to read file {}", filename);
        String::new()
    });

    let mut lexer = Lexer::new();

    lexer.lex(&file_contents);

    for err in lexer.errors() {
        eprintln!("{err}")
    }

    // For some reason jlox only exits on unterminated strings
    if lexer
        .errors()
        .iter()
        .any(|e| e.token() == rlox::lexer::Error::UnterminatedString)
    {
        std::process::exit(65)
    }

    let parser = Parser::new(lexer.tokens());
    let program = match parser.parse() {
        Ok(program) => program,
        Err(errors) => {
            for err in errors {
                eprintln!("{err}")
            }
            std::process::exit(65)
        }
    };

    let executor = Executor::with_stdout(program.decls());
    match executor.run() {
        Ok(..) => {}
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(70)
        }
    }
}
