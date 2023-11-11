use std::{collections::HashMap, fmt};

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
