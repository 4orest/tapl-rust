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

enum EvalProgress {
    Still(Box<Term>),
    NoRuleApplies,
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

fn is_booleanval(t: &Term) -> bool {
    match t {
        Term::TmTrue => true,
        Term::TmFalse => true,
        _ => false,
    }
}

fn eval1(t: &Term) -> Result<EvalProgress, String> {
    match t {
        Term::TmIf(t1, t2, t3) => match **t1 {
            Term::TmTrue => Ok(EvalProgress::Still(t2.clone())),
            Term::TmFalse => Ok(EvalProgress::Still(t3.clone())),
            _ => {
                let evaluated = eval(t1);
                match evaluated {
                    Ok(t) => Ok(EvalProgress::Still(Box::new(Term::TmIf(
                        Box::new(t),
                        t2.clone(),
                        t3.clone(),
                    )))),
                    Err(errmsg) => Err(errmsg),
                }
            }
        },
        Term::TmSucc(t) => {
            if is_booleanval(t) {
                Err("数であるべき項が数でない".to_string())
            } else if is_numericval(t) {
                Ok(EvalProgress::NoRuleApplies)
            } else {
                let evaluated = eval(t);
                match evaluated {
                    Ok(t) => Ok(EvalProgress::Still(Box::new(Term::TmSucc(Box::new(t))))),
                    Err(errmsg) => Err(errmsg),
                }
            }
        }
        Term::TmPred(t) => match &**t {
            Term::TmZero => Ok(EvalProgress::Still(Box::new(Term::TmZero))),
            Term::TmSucc(t) => {
                if is_numericval(&*t) {
                    Ok(EvalProgress::Still(t.clone()))
                } else {
                    Err("数であるべき項が数でない".to_string())
                }
            }
            _ => {
                let evaluated = eval(t);
                match evaluated {
                    Ok(t) => Ok(EvalProgress::Still(Box::new(Term::TmPred(Box::new(t))))),
                    Err(errmsg) => Err(errmsg),
                }
            }
        },
        Term::TmIsZero(t) => match &**t {
            Term::TmZero => Ok(EvalProgress::Still(Box::new(Term::TmTrue))),
            Term::TmSucc(t) => {
                if is_numericval(&*t) {
                    Ok(EvalProgress::Still(Box::new(Term::TmFalse)))
                } else {
                    Err("数であるべき項が数でない".to_string())
                }
            }
            _ => {
                let evaluated = eval(t);
                match evaluated {
                    Ok(t) => Ok(EvalProgress::Still(Box::new(Term::TmIsZero(Box::new(t))))),
                    Err(errmsg) => Err(errmsg),
                }
            }
        },
        _ => Ok(EvalProgress::NoRuleApplies),
    }
}

fn eval(t: &Term) -> Result<Term, String> {
    let t1 = eval1(t);
    match t1 {
        Ok(ep) => match ep {
            EvalProgress::Still(tt) => eval(&*tt),
            EvalProgress::NoRuleApplies => Ok(t.clone()),
        },
        Err(s) => Err(s),
    }
}

fn main() {
    let mut rl = Editor::<()>::new().unwrap();
    loop {
        if let Ok(readline) = rl.readline(">> ") {
            if let Some(e) = parse(&readline) {
                let result = eval(&e);
                match result {
                    Ok(t) => {
                        dbg!(t);
                    }
                    Err(errmsg) => {
                        println!("{}", errmsg);
                    }
                }
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
    fn test_parse_true() {
        let result = parser_true("true");
        assert_eq!(Ok(("", Term::TmTrue)), result);
    }

    #[test]
    fn test_parse_true_ng() {
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
    fn test_parse_false() {
        let result = parser_false("false");
        assert_eq!(Ok(("", Term::TmFalse)), result);
    }

    #[test]
    fn test_parse_false_ng() {
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

        assert_eq!(Ok(Term::TmZero), result);
    }

    #[test]
    fn eval_one() {
        let result = eval(&Term::TmSucc(Box::new(Term::TmZero)));

        assert_eq!(Ok(Term::TmSucc(Box::new(Term::TmZero))), result);
    }

    #[test]
    fn eval_pred_succ() {
        let result = eval(&Term::TmPred(Box::new(Term::TmSucc(Box::new(
            Term::TmZero,
        )))));

        assert_eq!(Ok(Term::TmZero), result);
    }
}
