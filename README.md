# Rlox

A tree-walking [Lox](https://github.com/munificent/craftinginterpreters) interpreter written in rust.

Built based on the [Codecrafters challenge](https://app.codecrafters.io/courses/interpreter/overview) and the [Crafting Interpreters book](https://craftinginterpreters.com/contents.html).

## Testing

Rlox has been tested to pass the jlox test suite provided in the Crafting Interpreters repository.

### Running the test suite 

```sh

# Build the interpreter
$ cargo build --release

# The official Crafting Interpreters repository is a submodule
$ cd craftinginterpreters

# Install the dart SDK
$ brew install dart@2.19
$ dart --version 
Dart SDK version: 2.19.6 (stable) (Tue Mar 28 13:41:04 2023 +0000) on "macos_arm64"

# Install the dart depencies
$ dart pub install

# Run the test suite. The behaviour of rlox matches jlox.
$ dart tool/bin/test.dart jlox --interpreter ../target/release/rlox
All 239 tests passed (556 expectations).

```


