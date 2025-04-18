use nom::{
    IResult,
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, multispace0},
};
use rustyline::Editor;

#[derive(Debug)]
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

fn eval1(t: &Term) -> EvalProgress {}

fn eval(t: &Term) -> Term {
    let t1 = eval1(t);
    match t1 {
        EvalProgress::Still(tt) => eval(&tt),
        EvalProgress::NoRuleApplies => t,
    }
}

fn main() {
    let mut rl = Editor::<()>::new().unwrap();
    loop {
        if let Ok(readline) = rl.readline(">> ") {
            if let Some(e) = parse(&readline) {
                println!(eval(&e));
            }
        } else {
            break;
        }
    }
}
