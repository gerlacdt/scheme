# Scheme Interpreter

This project implements a simplistic scheme interpreter in Rust for learning
purposes. It's based on [Sean Chen Blogs](https://medium.com/@seanchen).

### Usage

```bash
# compile a binary (see below)

# run the REPL
scheme repl

# run a file
scheme compile <file>
```

### Development

Install [Rust 1.75+](https://www.rust-lang.org/)

```bash
# build
cargo build

# run tests
cargo test

# run a file
cargo run compile <file>

# run the REPL
cargo run repl
```
