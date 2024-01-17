use crate::scheme::{Expression, SErr, SResult};
use std::rc::Rc;

pub fn parse<'a>(tokens: &'a [String]) -> SResult<(Expression, &'a [String])> {
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
    match token.as_ref() {
        "#t" => Expression::Bool(true),
        "#f" => Expression::Bool(false),
        _ => match token.parse() {
            Ok(n) => Expression::Number(n),
            Err(_) => Expression::Symbol(token.to_string().clone()),
        },
    }
}

pub fn parse_list_of_floats(args: &[Expression]) -> SResult<Vec<f64>> {
    args.iter().map(|x| parse_float(x)).collect()
}

fn parse_float(exp: &Expression) -> SResult<f64> {
    match exp {
        Expression::Number(n) => Ok(*n),
        _ => Err(SErr::Reason("Expected a number".to_string())),
    }
}

pub fn parse_list_of_symbols(args: Rc<Expression>) -> SResult<Vec<String>> {
    let list = match args.as_ref() {
        Expression::List(l) => Ok(l.clone()),
        _ => Err(SErr::Reason("expected args form to be a list".to_string())),
    }?;
    list.iter()
        .map(|x| match x {
            Expression::Symbol(s) => Ok(s.clone()),
            _ => Err(SErr::Reason(
                "expected symbols in the argument list".to_string(),
            )),
        })
        .collect()
}
