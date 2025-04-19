use nom::{
    IResult,
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, multispace0},
};
use rustyline::Editor;

#[derive(Debug, Clone)]
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
    Failure(&str),
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

fn parser_zero(c: &str) -> IResult<&str, Term> {
    let (c, _) = char('0')(c)?;

    Ok((c, Term::TmZero))
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
        parser_zero,
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

fn isnumericval(t: &Term) -> bool {
    match t {
        Term::TmZero => true,
        Term::TmSucc(t1) => isnumericval(t1),
        _ => false,
    }
}

fn eval1(t: &Term) -> EvalProgress {
    match t {
        Term::TmIf(t1, t2, t3) => {
            match **t1 {
                Term::TmTrue => EvalProgress::Still(t2.clone()),
                Term::TmFalse => EvalProgress::Still(t3.clone()),
                // エラー起きそう
                _ => {
                    let evaluated = eval(t1);
                    match evaluated {
                        Ok(t) => EvalProgress::Still(Box::new(Term::TmIf(
                            Box::new(t),
                            t2.clone(),
                            t3.clone(),
                        ))),
                        Err(errmsg) => EvalProgress::Failure(errmsg),
                    }
                }
            }
        }
        Term::TmSucc(t) => {
            let evaluated = eval(t);
            match evaluated {
                Ok(t) => EvalProgress::Still(Box::new(Term::TmSucc(Box::new(t)))),
                Err(errmsg) => EvalProgress::Failure(errmsg),
            }
        }
        Term::TmPred(t) => match **t {
            Term::TmZero => EvalProgress::Still(Box::new(Term::TmZero)),
            Term::TmSucc(t) => {
                if isnumericval(&*t) {
                    EvalProgress::Still(t)
                } else {
                    EvalProgress::Failure("数であるべき項が数でない")
                }
            }
            _ => {
                let evaluated = eval(t);
                match evaluated {
                    Ok(t) => EvalProgress::Still(Box::new(Term::TmPred(Box::new(t)))),
                    Err(errmsg) => EvalProgress::Failure(errmsg),
                }
            }
        },
        Term::TmIsZero(t) => match **t {
            Term::TmZero => EvalProgress::Still(Box::new(Term::TmTrue)),
            Term::TmSucc(t) => {
                if isnumericval(&*t) {
                    EvalProgress::Still(Box::new(Term::TmFalse))
                } else {
                    EvalProgress::Failure("数であるべき項が数でない")
                }
            }
            _ => {
                let evaluated = eval(t);
                match evaluated {
                    Ok(t) => EvalProgress::Still(Box::new(Term::TmIsZero(Box::new(t)))),
                    Err(errmsg) => EvalProgress::Failure(errmsg),
                }
            }
        },
        _ => EvalProgress::NoRuleApplies,
    }
}

fn eval(t: &Term) -> Result<Term, &str> {
    let t1 = eval1(t);
    match t1 {
        EvalProgress::Still(tt) => eval(&tt),
        EvalProgress::NoRuleApplies => Ok(t.clone()),
        EvalProgress::Failure(s) => Err(s),
    }
}

fn main() {
    let mut rl = Editor::<()>::new().unwrap();
    loop {
        if let Ok(readline) = rl.readline(">> ") {
            if let Some(e) = parse(&readline) {
                if let Ok(t) = eval(&e) {
                    dbg!(&t);
                }
            }
        } else {
            break;
        }
    }
}
