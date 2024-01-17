#![allow(dead_code, unused)]
use std::fs;
use std::io::prelude::*;
use std::rc::Rc;
use std::{
    collections::HashMap,
    fmt,
    io::{stdin, stdout},
};

use std::iter::Iterator;

use crate::environment::{init_env, Env};
use crate::evaluator::{eval, eval_forms};
use crate::parser::{parse, parse_list_of_floats, parse_list_of_symbols};
use crate::tokenizer::tokenize;

#[derive(Debug)]
pub enum SErr {
    Reason(String),
}

impl fmt::Display for SErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let str = match self {
            SErr::Reason(r) => r.clone(),
        };
        write!(f, "{}", str)
    }
}

pub type SResult<T> = Result<T, SErr>;

#[derive(Clone)]
pub struct SLambda {
    pub params: Rc<Expression>,
    pub body: Rc<Expression>,
}

#[derive(Clone)]
pub enum Expression {
    Bool(bool),
    Symbol(String),
    Number(f64),
    List(Vec<Expression>),
    Func(fn(&[Expression]) -> SResult<Expression>),
    Lambda(SLambda),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let str = match self {
            Expression::Bool(b) => {
                if *b {
                    "#t".to_string()
                } else {
                    "#f".to_string()
                }
            }
            Expression::Symbol(s) => s.clone(),
            Expression::Number(n) => n.to_string(),
            Expression::List(l) => {
                let chars: Vec<String> = l.iter().map(|c| c.to_string()).collect();
                format!("({})", chars.join(","))
            }
            Expression::Func(_) => "Function {}".to_string(),
            Expression::Lambda(_) => "Lambda: {}".to_string(),
        };
        write!(f, "{}", str)
    }
}

fn parse_eval(input: Vec<String>, env: &mut Env) -> SResult<Expression> {
    let (parsed, unparsed) = parse(&input)?;
    let evaluated = eval(&parsed, env)?;
    if !unparsed.is_empty() {
        parse_eval(unparsed.to_vec(), env)
    } else {
        Ok(evaluated)
    }
}

static PROMPT: &str = "scheme> ";

pub fn repl() {
    let env = &mut init_env();

    loop {
        print!("{}", PROMPT);
        stdout().flush().expect("failed to flush to stdout");

        let mut expr = String::new();
        stdin()
            .read_line(&mut expr)
            .expect("failed to read from stdin");

        if expr.trim() == "quit" {
            break;
        }

        let tokens = tokenize(&mut expr.chars().peekable());

        match parse_eval(tokens, env) {
            Ok(result) => println!("> {}", result),
            Err(e) => match e {
                SErr::Reason(msg) => println!("> Error: {}", msg),
            },
        }
    }
}

pub fn compile(path: &str) {
    let mut env = &mut init_env();
    let input = fs::read_to_string(path).expect("Can't read file");
    let tokens = tokenize(&mut input.chars().peekable());

    match parse_eval(tokens, env) {
        Ok(result) => println!("{}", result),
        Err(e) => match e {
            SErr::Reason(msg) => println!("scheme> ERROR: {}", msg),
        },
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    fn tokenize_helper(input: &str) -> Vec<String> {
        let expr = tokenize(&mut input.chars().peekable());
        expr
    }

    #[test]
    fn simple_expression_test() {
        let env = &mut init_env();
        let input = "(+ 2 6)";
        let expr = tokenize_helper(input);
        let actual = match parse_eval(expr, env).unwrap() {
            Expression::Number(n) => n,
            _ => 0.0,
        };

        let expected = 8.0;
        assert_eq!(expected, actual);
    }

    #[test]
    fn define_set_test() {
        let env = &mut init_env();

        let input1 = "(define my-num 42)";
        let expr1 = tokenize_helper(input1);
        parse_eval(expr1, env);
        let input2 = "(+ 3 my-num)";
        let expr2 = tokenize_helper(input2);

        let actual = match parse_eval(expr2, env).unwrap() {
            Expression::Number(n) => n,
            _ => 0.0,
        };

        let expected = 45.0;
        assert_eq!(expected, actual);
    }

    #[test]
    fn define_set_parse_lines_test() {
        let env = &mut init_env();
        let input = r#"
(define my-num 42)
(+ 3 my-num)
"#;
        let expr = tokenize_helper(input);
        let actual = match parse_eval(expr, env).unwrap() {
            Expression::Number(n) => n,
            _ => 0.0,
        };

        let expected = 45.0;
        assert_eq!(expected, actual);
    }

    #[test]
    fn compare_equals_test() {
        let env = &mut init_env();
        let input = "(= 1 1 1)";
        let expr = tokenize_helper(input);
        let actual = match parse_eval(expr, env).unwrap() {
            Expression::Bool(b) => b,
            _ => false,
        };

        assert!(actual);
    }

    #[test]
    fn compare_unequals_test() {
        let env = &mut init_env();
        let input = "(= 1 1 2)";
        let expr = tokenize_helper(input);

        let actual = match parse_eval(expr, env).unwrap() {
            Expression::Bool(b) => b,
            _ => panic!("expression could not be evaluated"),
        };

        assert!(!actual);
    }

    #[test]
    fn compare_greater_test() {
        let env = &mut init_env();
        let input = "(> 5 3 1)";
        let expr = tokenize_helper(input);
        let actual = match parse_eval(expr, env).unwrap() {
            Expression::Bool(b) => b,
            _ => panic!("expression could not be evaluated"),
        };

        assert!(actual);
    }

    #[test]
    fn compare_greater_than_test() {
        let env = &mut init_env();
        let input = "(>= 5 5 3 1)";
        let expr = tokenize_helper(input);

        let actual = match parse_eval(expr, env).unwrap() {
            Expression::Bool(b) => b,
            _ => panic!("expression could not be evaluated"),
        };

        assert!(actual);
    }

    #[test]
    fn compare_smaller_test() {
        let env = &mut init_env();
        let input = "(< 1 3 5)";
        let expr = tokenize_helper(input);

        let actual = match parse_eval(expr, env).unwrap() {
            Expression::Bool(b) => b,
            _ => panic!("expression could not be evaluated"),
        };

        assert!(actual);
    }

    #[test]
    fn compare_smaller_than_test() {
        let env = &mut init_env();
        let input = "(<= 1 1 3 5)";
        let expr = tokenize_helper(input);

        let actual = match parse_eval(expr, env).unwrap() {
            Expression::Bool(b) => b,
            _ => panic!("expression could not be evaluated"),
        };

        assert!(actual);
    }

    #[test]
    fn compare_with_variables_test() {
        let env = &mut init_env();
        let input = r#"
(define my-num 42)
(>= my-num 5 5 (+ 3 1))
"#;
        let expr = tokenize_helper(input);

        let actual = match parse_eval(expr, env).unwrap() {
            Expression::Bool(b) => b,
            _ => panic!("ERROR expression could not be evaluated"),
        };

        assert!(actual);
    }

    #[test]
    fn lambda_simple_test() {
        let env = &mut init_env();
        let input = r#"
(define add3 (lambda () (+ 1 2)))
(add3)
        "#;
        let expr = tokenize_helper(input);

        let actual = match parse_eval(expr, env).unwrap() {
            Expression::Number(n) => n,
            _ => panic!("ERROR expression could not be evaluated"),
        };

        let expected = 3.0;
        assert_eq!(expected, actual);
    }

    #[test]
    fn lambda_fib_test() {
        let env = &mut init_env();

        let input = r#"
(define fib (lambda (n) (if (< n 2) 1 (+ (fib (- n 1)) (fib (- n 2))))))
(fib 10)
        "#;
        let expr = tokenize_helper(input);

        let actual = match parse_eval(expr, env).unwrap() {
            Expression::Number(n) => n,
            _ => panic!("ERROR expression could not be evaluated"),
        };

        let expected = 89.0;
        assert_eq!(expected, actual);
    }

    #[test]
    fn compile_file_test() {
        let path = "./test_files/test.scm";
        compile(path);

        // assert!(false);  // uncomment if you want to see result in STDOUT
    }
}
