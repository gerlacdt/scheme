use crate::scheme::{compile, repl};
use clap::{Parser, Subcommand};

#[derive(Debug, Parser)]
pub struct Cli {
    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Debug, Subcommand)]
pub enum Commands {
    /// start the interactive environment REPL (Read Eval Print Loop), e.g. >scheme repl
    Repl,
    /// compile/run given file and print result, e.g. >scheme compile file.scm    
    Compile {
        /// relative file path which should be run
        file: String,
    },
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
