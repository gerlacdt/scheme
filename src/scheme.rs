#![allow(dead_code, unused)]
use std::io::prelude::*;
use std::{
    collections::HashMap,
    fmt,
    io::{stdin, stdout},
};

use std::iter::Iterator;

fn hello() {
    println!("scheme dummy function");
}

#[derive(Debug)]
enum SErr {
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

type SResult<T> = Result<T, SErr>;

#[derive(Clone)]
enum Expression {
    Symbol(String),
    Number(f64),
    List(Vec<Expression>),
    Func(fn(&[Expression]) -> SResult<Expression>),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let str = match self {
            Expression::Symbol(s) => s.clone(),
            Expression::Number(n) => n.to_string(),
            Expression::List(l) => {
                let chars: Vec<String> = l.iter().map(|c| c.to_string()).collect();
                format!("({})", chars.join(","))
            }
            Expression::Func(_) => "Function {}".to_string(),
        };
        write!(f, "{}", str)
    }
}

struct Env {
    operations: HashMap<String, Expression>,
}

fn tokenize(expression: String) -> Vec<String> {
    expression
        .replace("(", " ( ")
        .replace(")", " ) ")
        .split_whitespace()
        .map(|x| x.to_string())
        .collect()
}

fn parse<'a>(tokens: &'a [String]) -> SResult<(Expression, &'a [String])> {
    let (token, rest) = tokens
        .split_first()
        .ok_or(SErr::Reason("could not get token".to_string()))?;

    match &token[..] {
        "(" => read_sequence(rest),
        ")" => Err(SErr::Reason("unexpected )".to_string())),
        _ => Ok((parse_atom(token), rest)),
    }
}

fn read_sequence<'a>(tokens: &'a [String]) -> SResult<(Expression, &'a [String])> {
    let mut result: Vec<Expression> = vec![];
    let mut ts = tokens;

    loop {
        let (next, rest) = ts
            .split_first()
            .ok_or(SErr::Reason("could not find closing )".to_string()))?;

        if next == ")" {
            return Ok((Expression::List(result), rest));
        }

        let (exp, new_ts) = parse(&ts)?;
        result.push(exp);
        ts = new_ts;
    }
}

fn parse_atom(token: &str) -> Expression {
    match token.parse() {
        Ok(n) => Expression::Number(n),
        Err(_) => Expression::Symbol(token.to_string().clone()),
    }
}

fn parse_list_of_floats(args: &[Expression]) -> SResult<Vec<f64>> {
    args.iter().map(|x| parse_float(x)).collect()
}

fn parse_float(exp: &Expression) -> SResult<f64> {
    match exp {
        Expression::Number(n) => Ok(*n),
        _ => Err(SErr::Reason("Expected a number".to_string())),
    }
}

fn init_env() -> Env {
    let mut operations: HashMap<String, Expression> = HashMap::new();
    operations.insert(
        "+".to_string(),
        Expression::Func(|args: &[Expression]| -> Result<Expression, SErr> {
            let sum = parse_list_of_floats(args)?.iter().sum();
            Ok(Expression::Number(sum))
        }),
    );

    operations.insert(
        "*".to_string(),
        Expression::Func(|args: &[Expression]| -> Result<Expression, SErr> {
            let product = parse_list_of_floats(args)?.iter().product();
            Ok(Expression::Number(product))
        }),
    );

    operations.insert(
        "-".to_string(),
        Expression::Func(|args: &[Expression]| -> Result<Expression, SErr> {
            let floats = parse_list_of_floats(args)?;
            let (first, rest) = floats
                .split_first()
                .ok_or(SErr::Reason("expected at least one number".to_string()))?;
            let sum_of_rest: f64 = rest.iter().sum();
            Ok(Expression::Number(first - sum_of_rest))
        }),
    );

    Env { operations }
}

fn eval(exp: &Expression, env: &mut Env) -> SResult<Expression> {
    match exp {
        Expression::Symbol(s) => env
            .operations
            .get(s)
            .ok_or(SErr::Reason(format!("unexpected symbol: {}", s)))
            .map(|x| x.clone()),
        Expression::Number(_) => Ok(exp.clone()),
        Expression::List(l) => {
            let (first, args) = l
                .split_first()
                .ok_or(SErr::Reason("expected a non-empty list".to_string()))?;

            // TODO insert define, set! logic
            match eval_keyword(first, args, env) {
                Some(result) => result,
                None => {
                    let first_eval = eval(first, env)?;
                    match first_eval {
                        Expression::Func(f) => {
                            let args_eval = args
                                .iter()
                                .map(|x| eval(x, env))
                                .collect::<SResult<Vec<Expression>>>();
                            f(&args_eval?)
                        }
                        _ => Err(SErr::Reason("first form must be a function".to_string())),
                    }
                }
            }
        }
        Expression::Func(_) => Err(SErr::Reason("unexpected form".to_string())),
    }
}

fn eval_define(args: &[Expression], env: &mut Env) -> SResult<Expression> {
    if args.len() > 2 {
        return Err(SErr::Reason(
            "define keyword only accepts 2 forms".to_string(),
        ));
    }
    let (name, rest) = args
        .split_first()
        .ok_or(SErr::Reason("expected first form".to_string()))?;
    let name_str = match name {
        Expression::Symbol(s) => Ok(s.clone()),
        _ => Err(SErr::Reason(
            "expected first form to be a symbol".to_string(),
        )),
    }?;

    if env.operations.contains_key(&name_str) {
        return Err(SErr::Reason(
            "cannot overwrite a reserved operation".to_string(),
        ));
    }

    let value = rest
        .get(0)
        .ok_or(SErr::Reason("expected a value form".to_string()))?;
    let value_eval = eval(value, env)?;
    env.operations.insert(name_str, value_eval);
    Ok(name.clone())
}

fn eval_set(args: &[Expression], env: &mut Env) -> SResult<Expression> {
    if args.len() > 2 {
        return Err(SErr::Reason(
            "define keyword only accepts 2 forms".to_string(),
        ));
    }

    let (name, rest) = args
        .split_first()
        .ok_or(SErr::Reason("expected first form".to_string()))?;
    let name_str = match name {
        Expression::Symbol(s) => Ok(s.clone()),
        _ => Err(SErr::Reason("expected name to be a symbol".to_string())),
    }?;

    let value = rest
        .get(0)
        .ok_or(SErr::Reason("expected a value form".to_string()))?;
    let value_eval = eval(value, env)?;

    match env.operations.get(&name_str) {
        Some(_) => {
            env.operations.insert(name_str, value_eval);
        }
        None => {
            return Err(SErr::Reason(format!(
                "global variable {} is not defined",
                name_str
            )));
        }
    }
    Ok(name.clone())
}

fn eval_keyword(
    expr: &Expression,
    args: &[Expression],
    env: &mut Env,
) -> Option<SResult<Expression>> {
    match expr {
        Expression::Symbol(s) => match s.as_ref() {
            "define" => Some(eval_define(args, env)),
            "set!" => Some(eval_set(args, env)),
            _ => None,
        },
        _ => None,
    }
}

fn parse_eval(input: String, env: &mut Env) -> SResult<Expression> {
    let (parsed, _) = parse(&tokenize(input))?;
    let evaluated = eval(&parsed, env)?;
    Ok(evaluated)
}

fn parse_eval_lines(input: Vec<String>, env: &mut Env) -> SResult<Expression> {
    let mut result = Ok(Expression::Number(0.0));
    for line in input {
        result = parse_eval(line, env);
    }
    result
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

        match parse_eval(expr, env) {
            Ok(result) => println!("> {}", result),
            Err(e) => match e {
                SErr::Reason(msg) => println!("> Error: {}", msg),
            },
        }
    }
}
#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn simple_expression_test() {
        let env = &mut init_env();

        let expr = "(+ 2 6)".to_string();

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

        let expr1 = "(define my-num 42)".to_string();
        parse_eval(expr1, env);
        let expr2 = "(+ 3 my-num)".to_string();

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
        let expr1 = "(define my-num 42)".to_string();
        let expr2 = "(+ 3 my-num)".to_string();
        let exps = vec![expr1, expr2];

        let actual = match parse_eval_lines(exps, env).unwrap() {
            Expression::Number(n) => n,
            _ => 0.0,
        };

        let expected = 45.0;
        assert_eq!(expected, actual);
    }
}
