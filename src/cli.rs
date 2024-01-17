use crate::scheme::{compile, repl};
use clap::{Parser, Subcommand};

#[derive(Debug, Parser)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Debug, Subcommand)]
pub enum Commands {
    Repl,
    Compile { file: String },
}

pub fn start() {
    let args = Cli::parse();

    match args.command {
        Commands::Repl => {
            repl();
        }
        Commands::Compile { file } => compile(&file),
    }
}
