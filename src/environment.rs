use std::{collections::HashMap, fmt, rc::Rc};

use crate::{
    evaluator::eval_forms,
    parser::{parse_list_of_floats, parse_list_of_symbols},
    scheme::{Expression, SErr, SResult},
};

pub struct Env<'a> {
    pub builtins: HashMap<String, Expression>,
    pub operations: HashMap<String, Expression>,
    scope: Option<&'a Env<'a>>,
}

impl<'a> fmt::Display for Env<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut output: Vec<String> = vec![];
        for (key, value) in &self.operations {
            output.push(format!("{}  {}", key, value));
        }
        let str = format!("{}", output.join(","));
        write!(f, "{}", str)
    }
}

pub fn init_lambda_env<'a>(
    params: Rc<Expression>,
    args: &[Expression],
    outer: &'a mut Env,
) -> SResult<Env<'a>> {
    let symbols = parse_list_of_symbols(params)?;

    if symbols.len() != args.len() {
        return Err(SErr::Reason(format!(
            "expected {} args, got {}",
            symbols.len(),
            args.len()
        )));
    }

    let evaluated_forms = eval_forms(args, outer)?;
    let mut operations: HashMap<String, Expression> = HashMap::new();

    for (k, v) in symbols.iter().zip(evaluated_forms.iter()) {
        operations.insert(k.clone(), v.clone());
    }

    let new_env = Env {
        operations,
        builtins: outer.builtins.clone(),
        scope: Some(outer),
    };

    Ok(new_env)
}

pub fn env_get(s: &str, env: &Env) -> Option<Expression> {
    match env.builtins.get(s) {
        Some(expr) => Some(expr.clone()),
        None => match env.operations.get(s) {
            Some(expr) => Some(expr.clone()),
            None => match &env.scope {
                Some(outer) => env_get(s, &outer),
                None => None,
            },
        },
    }
}

macro_rules! comparison {
    ($check_fn:expr) => {{
        |args: &[Expression]| -> SResult<Expression> {
            let floats = parse_list_of_floats(args)?;
            let (first, rest) = floats
                .split_first()
                .ok_or(SErr::Reason("expected at least one number".to_string()))?;

            fn f(prev: &f64, ts: &[f64]) -> bool {
                match ts.first() {
                    Some(t) => $check_fn(prev, t) && f(t, &ts[1..]),
                    None => true,
                }
            }
            Ok(Expression::Bool(f(first, rest)))
        }
    }};
}

pub fn init_env<'a>() -> Env<'a> {
    let operations: HashMap<String, Expression> = HashMap::new();
    let mut builtins: HashMap<String, Expression> = HashMap::new();
    builtins.insert(
        "+".to_string(),
        Expression::Func(|args: &[Expression]| -> Result<Expression, SErr> {
            let sum = parse_list_of_floats(args)?.iter().sum();
            Ok(Expression::Number(sum))
        }),
    );

    builtins.insert(
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

    builtins.insert(
        "*".to_string(),
        Expression::Func(|args: &[Expression]| -> Result<Expression, SErr> {
            let product = parse_list_of_floats(args)?.iter().product();
            Ok(Expression::Number(product))
        }),
    );

    builtins.insert(
        "/".to_string(),
        Expression::Func(|args: &[Expression]| -> Result<Expression, SErr> {
            let floats = parse_list_of_floats(args)?;
            let first = *floats
                .first()
                .ok_or(SErr::Reason("expected at least one number".to_string()))?;
            let result = floats[1..]
                .iter()
                .filter(|x| **x != 0.0)
                .fold(first, |num, div| num / div);
            Ok(Expression::Number(result))
        }),
    );

    builtins.insert(
        "max".to_string(),
        Expression::Func(|args: &[Expression]| -> SResult<Expression> {
            let floats = parse_list_of_floats(args)?;
            let first = *floats.first().ok_or(SErr::Reason(
                "max operation expectes at least one number".to_string(),
            ))?;
            let max = floats.iter().fold(first, |acc, curr| acc.max(*curr));
            Ok(Expression::Number(max))
        }),
    );

    builtins.insert(
        "min".to_string(),
        Expression::Func(|args: &[Expression]| -> SResult<Expression> {
            let floats = parse_list_of_floats(args)?;
            let first = *floats.first().ok_or(SErr::Reason(
                "min operation expectes at least one number".to_string(),
            ))?;
            let min = floats.iter().fold(first, |acc, curr| acc.min(*curr));
            Ok(Expression::Number(min))
        }),
    );

    builtins.insert(
        "abs".to_string(),
        Expression::Func(|args: &[Expression]| -> SResult<Expression> {
            let float = parse_list_of_floats(args)?;
            if float.len() > 1 {
                return Err(SErr::Reason(
                    "abs operation expects a single number".to_string(),
                ));
            }
            Ok(Expression::Number(float[0].abs()))
        }),
    );

    builtins.insert(
        "expt".to_string(),
        Expression::Func(|args: &[Expression]| -> SResult<Expression> {
            let floats = parse_list_of_floats(args)?;
            if floats.len() != 2 {
                return Err(SErr::Reason(
                    "expt operation expects exactly two numbers".to_string(),
                ));
            }
            let operand = floats.first().unwrap();
            let exponent = floats.last().unwrap();

            Ok(Expression::Number(operand.powf(*exponent)))
        }),
    );

    builtins.insert(
        "round".to_string(),
        Expression::Func(|args: &[Expression]| -> SResult<Expression> {
            let float = parse_list_of_floats(args)?;
            if float.len() > 1 {
                return Err(SErr::Reason(
                    "round operation expects a single number".to_string(),
                ));
            }
            Ok(Expression::Number(float[0].round()))
        }),
    );

    builtins.insert(
        "=".to_string(),
        Expression::Func(comparison!(|a, b| a == b)),
    );

    builtins.insert(">".to_string(), Expression::Func(comparison!(|a, b| a > b)));
    builtins.insert("<".to_string(), Expression::Func(comparison!(|a, b| a < b)));
    builtins.insert(
        ">=".to_string(),
        Expression::Func(comparison!(|a, b| a >= b)),
    );
    builtins.insert(
        "<=".to_string(),
        Expression::Func(comparison!(|a, b| a <= b)),
    );

    Env {
        operations,
        builtins,
        scope: None,
    }
}
