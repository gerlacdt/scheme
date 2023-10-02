// our tokenize helper function strips out commas
fn tokenize(expr: &str) -> Vec<String> {
    expr.replace(",", "")
        .replace("[", " [ ")
        .replace("]", " ] ")
        .split_whitespace()
        .map(|x| x.to_string())
        .collect()
}

fn eval(op: &str, operands: &[u32]) -> u32 {
    // grab the first operand, and then the rest
    let (first, rest) = operands
        .split_first()
        .expect("Need at least one operand to be evaluated");

    let answer: u32 = match op {
        "!" => {
            if *first == 1 {
                0
            } else {
                1
            }
        }
        "&" => rest.iter().fold(*first, |acc, curr| acc & curr),
        "|" => rest.iter().fold(*first, |acc, curr| acc | curr),
        all => panic!("invalid operator: {} ---", all),
    };
    answer
}

// our function receives the expression as a vector or tokens
// and a position to start parsing the tokens at
// it returns a tuple with the first element as the answer
// and the second element as the length of the expression
fn parse_eval(tokens: &[String], mut pos: usize) -> (u32, usize) {
    // stores our answer
    let mut answer: u32 = 0;
    // stores our operation
    let mut op: &str = "";
    // stores our operands
    let mut operands: Vec<u32> = vec![];

    while pos < tokens.len() {
        // It's easier to work with a vector of string tokens
        let token = tokens.get(pos).expect("Position is out of bounds");

        match &token[..] {
            // an `[` means we recurse
            "[" => {
                let (tmp_answer, len) = parse_eval(&tokens, pos + 1);
                operands.push(tmp_answer);
                answer = tmp_answer;
                // increment our position by the length of the sub-expression so we don't double count
                pos += len - pos;
            }
            // an `]` means there are no more operands; we can evalute now
            "]" => {
                answer = eval(op, &operands);
                // println!("eval({}, {:?}) => {}", op, &operands, answer);
                pos += 1;
                break;
            }
            "|" | "&" | "!" => {
                op = token;
                pos += 1;
            }
            "0" | "1" => {
                operands.push(token.parse().unwrap());
                pos += 1;
            }
            _ => panic!("Unexpected token"),
        }
    }

    // println!("answer: {}, operands: {:?}", answer, &operands);
    (answer, pos)
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn eval_simple_test() {
        let expression = "[|, 1, 0]";

        // It's easier to work with a vector of strings in Rust
        let tokens = tokenize(expression);

        let actual = parse_eval(&tokens, 0).0;
        let expected = 1;
        assert_eq!(expected, actual);
    }

    #[test]
    fn eval_recursive_test() {
        let expression = "[|, [&, 1, 0], [!, 1]]";
        // It's easier to work with a vector of strings in Rust
        let tokens = tokenize(expression);

        let actual = parse_eval(&tokens, 0).0;
        let expected = 0;
        assert_eq!(expected, actual);
    }

    #[test]
    fn eval_deep_recursive_test() {
        let expression = "[|, [&, 1, [|, 1, 0]], [!, 1]]";
        // It's easier to work with a vector of strings in Rust
        let tokens = tokenize(expression);

        let actual = parse_eval(&tokens, 0).0;
        let expected = 1;
        assert_eq!(expected, actual);
    }
}
