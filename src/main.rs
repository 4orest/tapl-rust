use std::fmt;

use nom::{
    IResult,
    branch::alt,
    bytes::complete::tag,
    character::complete::{digit1, multispace0},
    error::ErrorKind,
};
use rustyline::Editor;

#[derive(Debug, Clone, PartialEq)]
enum Term {
    TmTrue,
    TmFalse,
    TmIf(Box<Term>, Box<Term>, Box<Term>),
    TmZero,
    TmSucc(Box<Term>),
    TmPred(Box<Term>),
    TmIsZero(Box<Term>),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = inner_fmt(self);
        write!(f, "{}", s)
    }
}

fn inner_fmt(t: &Term) -> String {
    if is_numericval(t) {
        return succ_stack_to_nat(t).unwrap().to_string();
    }

    let s = match t {
        Term::TmTrue => "true".to_string(),
        Term::TmFalse => "false".to_string(),
        Term::TmIf(t1, t2, t3) => {
            let s = "if ".to_string()
                + &inner_fmt(t1)
                + " then "
                + &inner_fmt(t2)
                + " else "
                + &inner_fmt(t3);

            s
        }
        Term::TmSucc(t) => "succ ".to_string() + &inner_fmt(t),
        Term::TmPred(t) => "pred ".to_string() + &inner_fmt(t),
        Term::TmIsZero(t) => "iszero ".to_string() + &inner_fmt(t),
        _ => "".to_string(),
    };

    s
}

fn parser_true(c: &str) -> IResult<&str, Term> {
    let (c, _) = tag("true")(c)?;

    Ok((c, Term::TmTrue))
}

fn parser_false(c: &str) -> IResult<&str, Term> {
    let (c, _) = tag("false")(c)?;

    Ok((c, Term::TmFalse))
}

fn parser_if(c: &str) -> IResult<&str, Term> {
    let (c, _) = tag("if")(c)?;
    let (c, _) = multispace0(c)?;
    let (c, t1) = parse_term(c)?;
    let (c, _) = multispace0(c)?;
    let (c, _) = tag("then")(c)?;
    let (c, _) = multispace0(c)?;
    let (c, t2) = parse_term(c)?;
    let (c, _) = multispace0(c)?;
    let (c, _) = tag("else")(c)?;
    let (c, _) = multispace0(c)?;
    let (c, t3) = parse_term(c)?;

    Ok((c, Term::TmIf(Box::new(t1), Box::new(t2), Box::new(t3))))
}

fn parser_nat(c: &str) -> IResult<&str, Term> {
    let (c1, v) = digit1(c)?;

    if let Ok(n) = v.parse::<u64>() {
        Ok((c1, nat_to_succ_stack(n)))
    } else {
        let err = nom::error::Error::new(c, ErrorKind::Fail);
        Err(nom::Err::Failure(err))
    }
}

fn nat_to_succ_stack(n: u64) -> Term {
    if n == 0 {
        Term::TmZero
    } else {
        Term::TmSucc(Box::new(nat_to_succ_stack(n - 1)))
    }
}

fn succ_stack_to_nat(t: &Term) -> Result<u64, String> {
    if !is_numericval(t) {
        return Err("数であるべき項が数でない".to_string());
    }

    match t {
        Term::TmZero => Ok(0),
        Term::TmSucc(t) => succ_stack_to_nat(t).and_then(|x| Ok(x + 1)),
        _ => Err("数であるべき項が数でない".to_string()),
    }
}

fn parser_succ(c: &str) -> IResult<&str, Term> {
    let (c, _) = tag("succ")(c)?;
    let (c, _) = multispace0(c)?;
    let (c, t) = parse_term(c)?;

    Ok((c, Term::TmSucc(Box::new(t))))
}

fn parser_pred(c: &str) -> IResult<&str, Term> {
    let (c, _) = tag("pred")(c)?;
    let (c, _) = multispace0(c)?;
    let (c, t) = parse_term(c)?;

    Ok((c, Term::TmPred(Box::new(t))))
}

fn parser_iszero(c: &str) -> IResult<&str, Term> {
    let (c, _) = tag("iszero")(c)?;
    let (c, _) = multispace0(c)?;
    let (c, t) = parse_term(c)?;

    Ok((c, Term::TmIsZero(Box::new(t))))
}

fn parse_term(c: &str) -> IResult<&str, Term> {
    let (c, _) = multispace0(c)?;

    let parsers = (
        parser_true,
        parser_false,
        parser_if,
        parser_nat,
        parser_succ,
        parser_pred,
        parser_iszero,
    );

    let result = alt(parsers)(c)?;
    Ok(result)
}

fn parse(c: &str) -> Option<Term> {
    match parse_term(c) {
        Ok((_, t)) => Some(t),
        Err(e) => {
            println!("{e}");
            None
        }
    }
}

fn is_numericval(t: &Term) -> bool {
    match t {
        Term::TmZero => true,
        Term::TmSucc(t1) => is_numericval(t1),
        _ => false,
    }
}

/// 適用できるルールが無い場合はNoneを返す
fn eval1(t: &Term) -> Option<Term> {
    match t {
        Term::TmIf(t1, t2, t3) => match &**t1 {
            Term::TmTrue => Some((**t2).clone()),
            Term::TmFalse => Some((**t3).clone()),
            _ => eval1(t1).and_then(|t| Some(Term::TmIf(Box::new(t), t2.clone(), t3.clone()))),
        },
        Term::TmSucc(t) => eval1(t).and_then(|t| Some(Term::TmSucc(Box::new(t)))),
        Term::TmPred(t) => match &**t {
            Term::TmZero => Some(Term::TmZero),
            Term::TmSucc(t) if is_numericval(t) => Some((**t).clone()),
            _ => eval1(t).and_then(|t| Some(Term::TmPred(Box::new(t)))),
        },
        Term::TmIsZero(t) => match &**t {
            Term::TmZero => Some(Term::TmTrue),
            Term::TmSucc(t) if is_numericval(t) => Some(Term::TmFalse),
            _ => eval1(t).and_then(|t| Some(Term::TmIsZero(Box::new(t)))),
        },
        _ => None,
    }
}

fn eval(t: &Term) -> Term {
    let t1 = eval1(t);
    match t1 {
        Some(t) => eval(&t),
        None => t.clone(),
    }
}

fn main() {
    let mut rl = Editor::<()>::new().unwrap();
    loop {
        if let Ok(readline) = rl.readline(">> ") {
            if let Some(e) = parse(&readline) {
                let result = eval(&e);
                println!("{}", result);
            }
        } else {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_true() {
        let result = parser_true("true");
        assert_eq!(Ok(("", Term::TmTrue)), result);
    }

    #[test]
    fn parse_true_ng() {
        let result = parser_true("false");
        assert_eq!(
            Err(nom::Err::Error(nom::error::Error::new(
                "false",
                nom::error::ErrorKind::Tag
            ))),
            result
        );
    }

    #[test]
    fn parse_false() {
        let result = parser_false("false");
        assert_eq!(Ok(("", Term::TmFalse)), result);
    }

    #[test]
    fn parse_false_ng() {
        let result = parser_false("true");
        assert_eq!(
            Err(nom::Err::Error(nom::error::Error::new(
                "true",
                nom::error::ErrorKind::Tag
            ))),
            result
        );
    }

    #[test]
    fn nat_to_succ_zero() {
        let result = nat_to_succ_stack(0);
        assert_eq!(Term::TmZero, result);
    }

    #[test]
    fn nat_to_succ_nonzero() {
        let result = nat_to_succ_stack(4);

        let expected = Term::TmSucc(Box::new(Term::TmSucc(Box::new(Term::TmSucc(Box::new(
            Term::TmSucc(Box::new(Term::TmZero)),
        ))))));

        assert_eq!(expected, result);
    }

    #[test]
    fn parse_zero() {
        let result = parser_nat("0");

        assert_eq!(Ok(("", Term::TmZero)), result);
    }

    #[test]
    fn parse_3() {
        let result = parser_nat("3");

        let expected = Ok((
            "",
            Term::TmSucc(Box::new(Term::TmSucc(Box::new(Term::TmSucc(Box::new(
                Term::TmZero,
            )))))),
        ));

        assert_eq!(expected, result);
    }

    #[test]
    fn parse_negative_int() {
        let result = parser_nat("-1");

        let expected = Err(nom::Err::Error(nom::error::Error::new(
            "-1",
            nom::error::ErrorKind::Digit,
        )));

        assert_eq!(expected, result);
    }

    #[test]
    fn eval_zero() {
        let result = eval(&Term::TmZero);

        assert_eq!(Term::TmZero, result);
    }

    #[test]
    fn eval_one() {
        let result = eval(&Term::TmSucc(Box::new(Term::TmZero)));

        assert_eq!(Term::TmSucc(Box::new(Term::TmZero)), result);
    }

    #[test]
    fn eval_pred_succ() {
        let result = eval(&Term::TmPred(Box::new(Term::TmSucc(Box::new(
            Term::TmZero,
        )))));

        assert_eq!(Term::TmZero, result);
    }

    #[test]
    fn succ_to_nat_zero() {
        let result = succ_stack_to_nat(&Term::TmZero);

        assert_eq!(result, Ok(0));
    }

    #[test]
    fn succ_to_nat_three() {
        let term = &Term::TmSucc(Box::new(Term::TmSucc(Box::new(Term::TmSucc(Box::new(
            Term::TmZero,
        ))))));

        let result = succ_stack_to_nat(term);

        assert_eq!(result, Ok(3));
    }

    #[test]
    fn succ_to_nat_err() {
        let term = &Term::TmTrue;
        let result = succ_stack_to_nat(term);

        assert_eq!(result, Err("数であるべき項が数でない".to_string()));
    }

    #[test]
    fn eval_psps() {
        let term = Term::TmPred(Box::new(Term::TmSucc(Box::new(Term::TmPred(Box::new(
            Term::TmSucc(Box::new(Term::TmSucc(Box::new(Term::TmZero)))),
        ))))));

        let result = eval(&term);

        assert_eq!(result, Term::TmSucc(Box::new(Term::TmZero)));
    }

    #[test]
    fn eval_spsp() {
        let term = Term::TmSucc(Box::new(Term::TmPred(Box::new(Term::TmSucc(Box::new(
            Term::TmPred(Box::new(Term::TmZero)),
        ))))));

        let result = eval(&term);

        assert_eq!(result, Term::TmSucc(Box::new(Term::TmZero)));
    }

    #[test]
    fn eval_iszero_true() {
        let term = Term::TmIsZero(Box::new(Term::TmZero));
        let result = eval(&term);

        assert_eq!(result, Term::TmTrue);
    }

    #[test]
    fn eval_iszero_false() {
        let term = Term::TmIsZero(Box::new(Term::TmSucc(Box::new(Term::TmZero))));
        let result = eval(&term);

        assert_eq!(result, Term::TmFalse);
    }

    #[test]
    fn eval_iszero_notnum() {
        let term = Term::TmIsZero(Box::new(Term::TmTrue));
        let result = eval(&term);

        assert_eq!(result, Term::TmIsZero(Box::new(Term::TmTrue)));
    }
}
