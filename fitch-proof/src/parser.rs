use std::collections::HashSet;
use std::iter;
use std::iter::from_fn;

use crate::data::*;
use crate::loc::{Location, Span, WithSpan};

type LToken = WithSpan<Token>;

/// This function takes a string slice and tries to parse it as a full proof.
///
/// If it succeeds, a vector of [LParsedProofNode]s is returned. If it does not succeed, then a nice error
/// message is returned.
///
/// For a specification of the grammar that is used for parsing, see the documentation of the
/// functions [parse_proof_line] and [parse_logical_expr].
pub fn parse_fitch_proof(proof: &str) -> Result<Vec<LParsedProofNode>, Diagnostic> {
    proof
        .lines()
        .enumerate()
        .filter_map(|(idx, line)| {
            if line.is_empty() {
                return None;
            }
            Some(match lex_with_line(line, Some(idx + 1)) {
                Ok(toks) => parse_proof_line(&toks),
                Err(err) => Err(err),
            })
        })
        .collect()
}

/// This function parses the list of strings that should be seen as a variable. This list should
/// simply be a string slice like this: "x,y,z", which means that "x", "y" and "z" are the strings
/// that should be seen as a variable.
///
/// Note that the list should not contain duplicates and that it should not contain a 'variable'
/// of which the name starts with an uppercase letter. If this happens, then an error message is
/// returned. An error message is returned in all cases in which the parsing failed.
///
/// If the parsing is successful, a [HashSet] containing the allowed variable names is returned.
pub fn parse_allowed_variable_names(allowed_var_names: &str) -> Result<HashSet<String>, String> {
    let toks = match lex(allowed_var_names) {
        Ok(toks) => toks,
        Err(err) => {
            return Err(format!(
                "failure when lexing list of allowed variable names: {}",
                err.message
            ))
        }
    };
    let err_str = "the list of allowed variable names could not be parsed".to_string();

    // additional check, does not hurt
    if toks.iter().any(|tok| !matches!(tok.value(), Token::Name(_) | Token::Comma)) {
        return Err(err_str);
    }

    let mut allowed_variable_names: HashSet<String> = HashSet::from([]);
    let mut rem_toks = toks.as_slice();

    loop {
        let Some(first_tok) = rem_toks.first() else {
            return Err(err_str);
        };
        let Token::Name(var_name) = first_tok.value() else {
            return Err(err_str);
        };
        if !var_name.chars().next().unwrap().is_ascii_lowercase() {
            return Err(format!("the list of allowed variable names could not be parsed: a variable name must start with a lowercase letter: {}", var_name));
        }
        if allowed_variable_names.contains(var_name) {
            return Err(format!(
                "the list of allowed variable names contains duplicates: {}",
                var_name
            ));
        }
        allowed_variable_names.insert(var_name.to_string());
        if rem_toks.len() == 1 {
            break;
        }
        if !matches!(rem_toks[1].value(), Token::Comma) {
            return Err(err_str);
        }
        rem_toks = &rem_toks[2..];
    }
    Ok(allowed_variable_names)
}

/// This function parses a *logical expression* from a String.
///
/// If it succeeds, a [Wff] is returned. Otherwise, a nice error message is returned.
///
/// The grammar: (brackets denote tokens; {} is EBNF notation for 0 or more times)
///
/// ```notrust
/// <E1> ::=
///            <E2>
///          | <E2> and <E2> {and <E2>}
///          | <E2> or <E2> {or <E2>}
///          | <E2> implies <E2>
///          | <E2> bicond <E2>
///
/// <E2> ::=
///            <E3>
///          | <Term> equals <Term>
///
/// <E3> ::=
///            <PredicateName> <ArgList>
///          | <AtomicPropositionName>
///          | ( <E1> )
///          | forall <VariableOrConstantName> <E3>
///          | exists <VariableOrConstantName> <E3>
///          | not <E3>
///          | bottom
///
/// <Term> ::=
///              <FunctionName> <ArgList>
///            | <VariableOrConstantName>
///
/// <ArgList> ::= ( <Term> {, <Term>} )
///
/// <FunctionName> : some string starting with a lowercase letter
/// <VariableOrConstantName> : some string starting with a lowercase letter
/// <PredicateName> : some string starting with an UPPERCASE letter
/// <AtomicPropositionName> : some string starting with an UPPERCASE letter
/// ```
pub fn parse_logical_expression_string(expr: &str) -> Option<LWff> {
    lex(expr).and_then(|toks| parse_logical_expr(&toks)).ok()
}

/* ----------------- PRIVATE -------------------*/

/// This is an enum containing tokens. The lexer converts a [String] to a vector of [Token]s, which
/// can then be used by the parser.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Name(String),
    LPar,
    RPar,
    Forall,
    Exists,
    And,
    Or,
    Implies,
    Bicond,
    Not,
    Bottom,
    Comma,
    Dot,
    Equals,
    Number(usize),
    ConseqVertBar(usize),
    Colon,
    Dash,
    LSqBracket,
    RSqBracket,
}

/// Generate a list of [Token]s from a [String]. If the lexer fails, a nice error message is returned.
fn lex(input: &str) -> Result<Vec<LToken>, Diagnostic> {
    lex_with_line(input, None)
}

fn lex_with_line(input: &str, line_number: Option<usize>) -> Result<Vec<LToken>, Diagnostic> {
    let mut toks: Vec<LToken> = Vec::new();
    let mut input_iter = input.chars().peekable();
    let line = line_number.unwrap_or(1);
    let mut pos = Location::new(None, line, 1);

    while let Some(ch) = input_iter.next() {
        let start = pos.clone();
        pos.next_column();
        match ch {
            ' ' | '\t' => {} // ignore spaces
            '(' => toks.push(WithSpan::new(Token::LPar, Span::new(start, pos.clone()))),
            ')' => toks.push(WithSpan::new(Token::RPar, Span::new(start, pos.clone()))),
            '\u{2200}' => toks.push(WithSpan::new(Token::Forall, Span::new(start, pos.clone()))),
            '\u{2203}' => toks.push(WithSpan::new(Token::Exists, Span::new(start, pos.clone()))),
            '&' | '*' | '\u{2227}' => {
                toks.push(WithSpan::new(Token::And, Span::new(start, pos.clone())))
            }
            '+' | '\u{2228}' => toks.push(WithSpan::new(Token::Or, Span::new(start, pos.clone()))),
            '\u{2192}' => toks.push(WithSpan::new(Token::Implies, Span::new(start, pos.clone()))),
            '\u{2194}' => toks.push(WithSpan::new(Token::Bicond, Span::new(start, pos.clone()))),
            '!' | '\u{00AC}' => toks.push(WithSpan::new(Token::Not, Span::new(start, pos.clone()))),
            ',' => toks.push(WithSpan::new(Token::Comma, Span::new(start, pos.clone()))),
            '.' => toks.push(WithSpan::new(Token::Dot, Span::new(start, pos.clone()))),
            '=' => toks.push(WithSpan::new(Token::Equals, Span::new(start, pos.clone()))),
            //a variable name begins with a letter and contains only other letters
            //TODO: consider using c.is_ascii_alphanumeric())
            'a'..='z' | 'A'..='Z' => {
                let name = iter::once(ch) // push back the read char
                    .chain(from_fn(|| {
                        input_iter.by_ref().next_if(|c| c.is_ascii_alphabetic())
                    }))
                    .collect::<String>();
                pos.advance_by(name.len() - 1); // advance the position information
                let token = match name.as_str() {
                    "and" => Token::And,
                    "or" => Token::Or,
                    "not" | "neg" => Token::Not,
                    "impl" => Token::Implies,
                    "bic" => Token::Bicond,
                    "bot" => Token::Bottom,
                    "fa" => Token::Forall,
                    "ex" => Token::Exists,
                    _ => Token::Name(name),
                };
                toks.push(WithSpan::new(token, Span::new(start, pos.clone())));
            }
            '1'..='9' => {
                let num_str = iter::once(ch)
                    .chain(from_fn(|| input_iter.by_ref().next_if(|c| c.is_ascii_digit())))
                    .collect::<String>();
                let err = "there was an integer bigger than 999999999".to_string();
                pos.advance_by(num_str.len() - 1);
                match num_str.parse::<usize>() {
                    Ok(n) if n <= 999_999_999 => {
                        toks.push(WithSpan::new(Token::Number(n), Span::new(start, pos.clone())))
                    }
                    _ => return Err(Diagnostic::new(err, Span::new(start, pos.clone()))),
                }
            }
            '|' => {
                let full_bar_str: String = iter::once(ch)
                    .chain(from_fn(|| input_iter.by_ref().next_if(|c| *c == '|' || *c == ' ')))
                    .collect();
                // how many bares we actually have
                let count = full_bar_str.chars().filter(|c| *c == '|').count();
                pos.advance_by(full_bar_str.len() - 1);

                toks.push(WithSpan::new(
                    Token::ConseqVertBar(count),
                    Span::new(start, pos.clone()),
                ));
            }
            ':' => toks.push(WithSpan::new(Token::Colon, Span::new(start, pos.clone()))),
            '[' => toks.push(WithSpan::new(Token::LSqBracket, Span::new(start, pos.clone()))),
            ']' => toks.push(WithSpan::new(Token::RSqBracket, Span::new(start, pos.clone()))),
            '⊥' => toks.push(WithSpan::new(Token::Bottom, Span::new(start, pos.clone()))),
            '-' if input_iter.peek() == Some(&'>') => {
                input_iter.next(); /* consume > */
                pos.advance_by(1);
                toks.push(WithSpan::new(Token::Implies, Span::new(start, pos.clone())));
            }
            '-' => toks.push(WithSpan::new(Token::Dash, Span::new(start, pos.clone()))),
            _ => {
                let mut err: String = "invalid character found: ".to_owned();
                err.push(ch);
                return Err(Diagnostic::new(err, Span::new(start, pos.clone())));
            }
        }
    }

    Ok(toks)
}

/// This function parses a *logical expression* from a list of [Token]s.
///
/// If it succeeds, a [Wff] is returned. Otherwise, a nice error message is returned.
///
/// The grammar: see documentation of [parser::parse_logical_expression_string].
///
/// if the resulting Diagnostic has location: None, then we take it that the whole line is at fault
/// TODO: more precise error location
fn parse_logical_expr(toks: &[LToken]) -> Result<LWff, Diagnostic> {
    if toks.is_empty() {
        return Err(Diagnostic::new(
            "parse_logical_expression: no tokens to parse".to_string(),
            Span::dummy(),
        ));
    }
    let from_span = toks.first().unwrap().span();
    let to_span = toks.last().unwrap().span();
    if let Some((wff, rem_toks)) = parse_e1(toks) {
        // check that there are no remaining tokens left
        if rem_toks.is_empty() {
            return Ok(wff);
        } else {
            return Err(Diagnostic::new(
                format!("failed to parse logical expression"),
                Span::cover(from_span, to_span),
            ));
        }
    } else {
        return Err(Diagnostic::new(
            format!("failed to parse logical expression"),
            Span::cover(from_span, to_span),
        ));
    }
}

/// Parse an `<E1>` as defined by the grammar specified in the documentation of [parse_logical_expr].
fn parse_e1(toks: &[LToken]) -> Option<(LWff, &[LToken])> {
    // always accept the first <E2>
    let (first, mut rem) = parse_e2(toks)?;
    if rem.is_empty() {
        // Derivation <E1> => <E2>
        return Some((first, rem));
    }

    // it is safe to call unwrap here because we checked for the emptyness of `rem`
    // in the lines above
    match rem.first().unwrap().value() {
        // <E1> => <E2> implies <E2>
        Token::Implies => {
            let (rhs, rem_rest) = parse_e2(rem.get(1..)?)?;
            let span = consumed_span(toks, rem_rest);
            Some((WithSpan::new(Wff::Implies(Box::new(first), Box::new(rhs)), span), rem_rest))
        }
        // <E1> => <E2> bicond <E2>
        Token::Bicond => {
            let (rhs, rem_rest) = parse_e2(rem.get(1..)?)?;
            let span = consumed_span(toks, rem_rest);
            Some((WithSpan::new(Wff::Bicond(Box::new(first), Box::new(rhs)), span), rem_rest))
        }
        // <E1> => <E2> and <E2> [and <E2>]
        Token::And => {
            let mut conjuncts = vec![first];
            while !rem.is_empty() && matches!(rem[0].value(), Token::And) {
                let (next, rest) = parse_e2(rem.get(1..)?)?;
                conjuncts.push(next);
                rem = rest;
            }
            // it is safe to unwrap here because we constructed `conjuncts` as non-empty
            let span = consumed_span(toks, rem);
            Some((WithSpan::new(Wff::And(conjuncts), span), rem))
        }
        // <E1> => <E2> or <E2> [or <E2>]
        Token::Or => {
            let mut disjuncts = vec![first];
            while !rem.is_empty() && matches!(rem[0].value(), Token::Or) {
                let (next, rest) = parse_e2(rem.get(1..)?)?;
                disjuncts.push(next);
                rem = rest;
            }
            // it is safe to unwrap here because we constructed `disjuncts` as non-empty
            let span = consumed_span(toks, rem);
            Some((WithSpan::new(Wff::Or(disjuncts), span), rem))
        }
        // there are still remaining tokens left, but we cannot parse further
        _ => Some((first, rem)),
    }
}

/// Parse an `<E2>` as defined by the grammar specified in the documentation of [parse_logical_expr].
fn parse_e2(toks: &[LToken]) -> Option<(LWff, &[LToken])> {
    // <E2> => <E3>
    if let Some((wff, rem_toks)) = parse_e3(toks) {
        return Some((wff, rem_toks));
    }

    // <E2> => <Term> equals <Term>
    if let Some((term1, rem_toks1)) = parse_term(toks) {
        if matches!(rem_toks1.first()?.value(), Token::Equals) {
            if let Some((term2, rem_toks2)) = parse_term(rem_toks1.get(1..)?) {
                let span = consumed_span(toks, rem_toks2);
                return Some((WithSpan::new(Wff::Equals(term1, term2), span), rem_toks2));
            }
        }
    }

    None
}

fn span_of_tokens(toks: &[LToken]) -> Span {
    let first = toks.first().expect("list cannot be empty");
    let last = toks.first().expect("list cannot be empty");

    Span::cover(first.span(), last.span())
}

fn consumed_span(toks: &[LToken], rem_toks: &[LToken]) -> Span {
    let consumed = toks.len().checked_sub(rem_toks.len()).expect("list cannot be empty");
    if consumed == 0 {
        return Span::dummy();
    }

    span_of_tokens(&toks[..consumed])
}

/// Parse an `<E3>` as defined by the grammar specified in the documentation of [parse_logical_expr].
fn parse_e3(toks: &[LToken]) -> Option<(LWff, &[LToken])> {
    let first = toks.first()?;
    match first.value() {
        // <E3> => <PredicateName> <ArgList> | <AtomicPropositionName>
        // check if the name starts with a capital letter
        Token::Name(name) if name.chars().next()?.is_uppercase() => {
            if let Some((terms, rem_toks)) = parse_arg_list(&toks[1..]) {
                let span = consumed_span(toks, rem_toks);
                Some((WithSpan::new(Wff::PredApp(name.to_string(), terms), span), rem_toks))
            } else {
                Some((
                    WithSpan::new(Wff::Atomic(name.to_string()), first.span().clone()),
                    &toks[1..],
                ))
            }
        }
        // <E3> => ( <E1> )
        Token::LPar => {
            let (expr, rem_toks) = parse_e1(&toks[1..])?;
            if matches!(rem_toks.first()?.value(), Token::RPar) {
                let rem_toks = &rem_toks[1..];
                let span = consumed_span(toks, rem_toks);
                let WithSpan {
                    value,
                    ..
                } = expr;
                Some((WithSpan::new(value, span), rem_toks))
            } else {
                None
            }
        }
        // <E3> => forall <VarName> <E3>
        Token::Forall => {
            let (var, rem_toks1) = parse_name(&toks[1..])?;
            let (expr, rem_toks2) = parse_e3(rem_toks1)?;
            let span = consumed_span(toks, rem_toks2);
            Some((WithSpan::new(Wff::Forall(var.to_owned(), Box::new(expr)), span), rem_toks2))
        }
        // <E3> => exists <VarName> <E3>
        Token::Exists => {
            let (var, rem_toks1) = parse_name(&toks[1..])?;
            let (expr, rem_toks2) = parse_e3(rem_toks1)?;
            let span = consumed_span(toks, rem_toks2);
            Some((WithSpan::new(Wff::Exists(var.to_owned(), Box::new(expr)), span), rem_toks2))
        }
        // <E3> => bottom
        Token::Bottom => Some((WithSpan::new(Wff::Bottom, first.span().clone()), &toks[1..])),
        // <E3> => not <E3>
        Token::Not => {
            let (expr, rem_toks) = parse_e3(&toks[1..])?;
            let span = consumed_span(toks, rem_toks);
            Some((WithSpan::new(Wff::Not(Box::new(expr)), span), rem_toks))
        }
        _ => None,
    }
}

/// Parse a `<Term>` as defined by the grammar specified in the documentation of [parse_logical_expr].
fn parse_term(toks: &[LToken]) -> Option<(LTerm, &[LToken])> {
    let first = toks.first()?;
    let (name, rem_toks) = parse_name(toks)?;

    match parse_arg_list(rem_toks) {
        Some((terms, rem_toks)) => {
            let span = consumed_span(toks, rem_toks);
            Some((WithSpan::new(Term::FuncApp(name.to_string(), terms), span), rem_toks))
        }
        None => {
            Some((WithSpan::new(Term::Atomic(name.to_string()), first.span().clone()), rem_toks))
        }
    }
}

fn parse_name(toks: &[LToken]) -> Option<(&String, &[LToken])> {
    let next = toks.first()?;
    let Token::Name(var) = next.value() else {
        return None;
    };
    if !var.chars().next().is_some_and(|c| c.is_ascii_lowercase()) {
        return None;
    }
    Some((var, &toks[1..]))
}

/// Parse an `<ArgList>` as defined by the grammar specified in the documentation of [parse_logical_expr].
fn parse_arg_list(toks: &[LToken]) -> Option<(Vec<LTerm>, &[LToken])> {
    if !matches!(toks.first()?.value(), Token::LPar) {
        return None;
    }

    let mut terms: Vec<LTerm> = vec![];

    if let Some((term, mut rem_toks)) = parse_term(&toks[1..]) {
        terms.push(term);
        while matches!(rem_toks.first()?.value(), Token::Comma) {
            if let Some((term2, rem_rem_toks)) = parse_term(rem_toks.get(1..)?) {
                terms.push(term2);
                rem_toks = rem_rem_toks;
            } else {
                return None;
            }
        }

        if matches!(rem_toks.first()?.value(), Token::RPar) {
            Some((terms, &rem_toks[1..]))
        } else {
            None
        }
    } else {
        None
    }
}

/// This function parses one proof line from a list of [Token]s.
///
/// The grammar of a Fitch proof:
///
/// ```notrust
/// <FitchProof> is several <FitchProofLine>s separated by newline
/// <FitchProofLine> ::=
///                        <num> '|' { '|' } <E1> <Justification>             // non-premise
///                      | <num> '|' { '|' } <E1>                             // premise
///                      | <num> '|' { '|' } '[' <ConstantName> ']' [ <E1> ]  // premise with box
///                      | '|' { '|' } - { - }                                // fitch bar
///                      | '|' { '|' }                                        // empty line
///
/// <ConstantName> : some string starting with lowercase letter
///
/// <E1> is a full logical expression as parsed by the function parse_logical_expression_string();
/// the grammar for <E1> is defined in logic_expr.parser.rs.
///
/// <num> is a non-negative decinal integer
///
/// <Justification> ::=
///                      | Reit: <num>
///                      | And Intro: <num> {, <num>}
///                      | And Elim: <num>
///                      | Or Intro: <num>
///                      | Or Elim: <num>, <numrange> {, <numrange>}
///                      | Implies Intro: <numrange>
///                      | Implies Elim: <num>, <num>
///                      | Bicond Intro: <numrange>, <numrange>
///                      | Bicond Elim: <num>, <num>
///                      | Not Intro: <numrange>
///                      | Not Elim: <num>
///                      | Equals Intro
///                      | Equals Elim: <num>, <num>
///                      | Bottom Intro: <num>, <num>
///                      | Bottom Elim: <num>
///                      | Forall Intro: <numrange>
///                      | Forall Elim: <num>
///                      | Exists Intro: <num>
///                      | Exists Elim: <num>, <numrange>
///
/// ```
///
/// Note that Fitch proof lines are not very straightforward to parse, because it can be difficult
/// to find the separation between the `<E1>` and the `<Justification>`. However, note that the Colon
/// token only appears in the `<Justification>`, not in `<E1>`, `<num>` or `<ConstantName>`. Hence, if we
/// want to parse a proof line, we first check whether there is a colon token in it. If there is,
/// then we parse the justification first. If the line ends with =Intro, then we also parse the
/// justification first (=Intro is the only justification without colon). For the rest, everything
/// can just be done normally from left to right.
///
/// if the resulting Diagnostic has span: None, then we take it that the whole line is at fault
fn parse_proof_line(toks: &[LToken]) -> Result<LParsedProofNode, Diagnostic> {
    if toks.is_empty() {
        return Err(Diagnostic::new("proof line appears to be empty".to_string(), Span::dummy()));
    }

    let has_colon = toks.iter().any(|t| matches!(t.value(), Token::Colon));
    let ends_with_intro = toks.len() >= 2
        && matches!(toks.last().unwrap().value(), Token::Name(name) if name == "Intro")
        && matches!(toks[toks.len() - 2].value(), Token::Equals);

    if has_colon || ends_with_intro {
        // we know that in this case, <FitchProofLine> ::= <num> '|' { '|' } <E1> <Justification>
        // since only a line with a Justification can legally contain a colon token or end with =Intro
        parse_line_with_justification(toks)
    } else {
        // Otherwise we parse a line without a justification (e.g. a premise)
        parse_line_without_justification(toks)
    }
}

/// Assumes that `toks` is non-empty
fn parse_line_with_justification(toks: &[LToken]) -> Result<LParsedProofNode, Diagnostic> {
    let number_tok = toks.first();
    let depth_tok = toks.get(1);

    let line_num = match number_tok.map(|t| t.value()) {
        Some(Token::Number(line_num)) => {
            WithSpan::new(LineNumber::Explicit(*line_num), number_tok.unwrap().span.clone())
        }
        Some(Token::Dot) => WithSpan::new(LineNumber::Auto, number_tok.unwrap().span.clone()),

        _ => {
            return Err(Diagnostic::new(
                "a proof line with justification must start with a line number".to_string(),
                number_tok.map(WithSpan::span).unwrap_or(&Span::dummy()).clone(),
            ))
        }
    };
    let Some(Token::ConseqVertBar(depth)) = depth_tok.map(|t| t.value()) else {
        return Err(Diagnostic::new(
            "after the line number, there should be at least one vertical bar".to_string(),
            depth_tok.map(WithSpan::span).unwrap_or(&Span::dummy()).clone(),
        ));
    };

    let first_colon = toks.iter().enumerate().find(|(_, t)| matches!(t.value(), Token::Colon));

    let (colon_index, ot) = match first_colon {
        Some((ci, t)) => (ci, Some(t)),
        None => (toks.len(), None),
    };

    if colon_index < 4 {
        return Err(Diagnostic::new("failed to parse proof line. The proof line contains a colon, but this colon appears so early that it cannot possibly be a justification".to_string(), 
            ot.map(WithSpan::span).unwrap_or(&Span::dummy()).clone()));
    }

    let (before_just, just_slice) = if let Token::Name(name) = toks[colon_index - 1].value() {
        match name.as_str() {
            "Reit" => (&toks[..colon_index - 1], &toks[colon_index - 1..]),
            "Intro" | "Elim" => (&toks[..colon_index - 2], &toks[colon_index - 2..]),
            _ => {
                return Err(Diagnostic::new(format!("failed to parse justification. Expected 'Reit', 'Intro' or 'Elim', found '{name}'. Note that capitalization matters!"), toks[colon_index - 1].span().clone()));
            }
        }
    } else {
        return Err(Diagnostic::new("sentence contains a colon, which was expected to be preceded by 'Intro', 'Elim' or 'Reit', but the parser did not find any of these.".to_string(),toks[colon_index - 1].span().clone()));
    };

    let sentence_tokens = before_just.get(2..).unwrap_or(&[]);
    let sentence = parse_logical_expr(sentence_tokens)?;
    let justification = parse_justification(just_slice)?;

    let node_span = span_of_tokens(toks);
    Ok(WithSpan::new(
        ParsedProofNode::Numbered(ParsedNumberedLine {
            line_num,
            depth: *depth,
            sentence: Some(sentence),
            justification: Some(justification),
            boxed_constant: None,
        }),
        node_span,
    ))
}

/// Assumes that `toks` is non-empty
/// if the resulting Diagnostic has span: None, then we take it that the whole line is at fault
/// TODO: more precise error span for the boxed constants case
fn parse_line_without_justification(toks: &[LToken]) -> Result<LParsedProofNode, Diagnostic> {
    // Now we must be in one if these cases:
    //  1) opening a new scope
    //     <num> '|' { '|' } <E1>
    //  2) opening a new scope with a boxed constant
    //     <num> '|' { '|' } '[' <ConstantName> ']' [ <E1> ]
    //  3) Fitch bar
    //     '|' { '|' } - { - }
    //  4) Empty line
    //     '|' { '|' }
    let first = toks.first().unwrap();
    match first.value() {
        Token::Number(_) | Token::Dot => {
            let line_num = match first.value() {
                Token::Number(nr) => WithSpan::new(LineNumber::Explicit(*nr), first.span.clone()),
                Token::Dot => WithSpan::new(LineNumber::Auto, first.span.clone()),
                _ => unreachable!(),
            };

            // we must be in the case 1 and 2
            let Some(Token::ConseqVertBar(depth)) = toks.get(1).map(|x| x.value()) else {
                return Err(Diagnostic::new(
                    "after the line number, there should be at least one vertical bar".to_string(),
                    first.span().clone(),
                ));
            };

            // try to parse a boxed constant
            // in this case we
            let mut const_between: Option<LTerm> = None;

            // first positon in `toks` where we start with the formula
            // this going to be either 2 ( if there is no boxed constant )
            // or 5 (if there is one )
            let expression_start = if let (
                Some(Token::LSqBracket),
                Some(name_tok),
                Some(Token::RSqBracket),
            ) =
                (toks.get(2).map(|x| x.value()), toks.get(3), toks.get(4).map(|x| x.value()))
            {
                let name_span = name_tok.span().clone();
                let Token::Name(name) = name_tok.value() else {
                    return Err(Diagnostic::new(
                        "boxed constants must be names".to_string(),
                        name_span.clone(),
                    ));
                };
                if !name.chars().next().unwrap_or('U').is_ascii_lowercase() {
                    return Err(Diagnostic::new("a boxed constant must be a constant; it should start with a lowercase letter".to_string(), name_span.clone()));
                }

                const_between = Some(WithSpan::new(Term::Atomic(name.to_string()), name_span));
                // the line introduces a boxed constant and nothing else
                if toks.len() == 5 {
                    let node_span = span_of_tokens(toks);
                    return Ok(WithSpan::new(
                        ParsedProofNode::Numbered(ParsedNumberedLine {
                            line_num,
                            depth: *depth,
                            sentence: None,
                            justification: None,
                            boxed_constant: const_between,
                        }),
                        node_span,
                    ));
                }
                5
            } else {
                2
            };

            let has_brackets = toks.iter().any(|t| matches!(t.value(), Token::LSqBracket))
                || toks.iter().any(|t| matches!(t.value(), Token::RSqBracket));
            if has_brackets && expression_start != 5 {
                return Err(Diagnostic::new("failed when trying to read boxed constant (if you did not intend to introduce a boxed constant in this proof line, remove '[' and ']').".to_string(), span_of_tokens(toks)));
            }

            let sentence_tokens = &toks[expression_start..];
            let wff = if sentence_tokens.is_empty() {
                None
            } else {
                Some(parse_logical_expr(sentence_tokens)?)
            };

            if wff.is_none() && const_between.is_none() {
                return Err(Diagnostic::new(
                    "a proof line must contain a sentence or introduce a boxed constant"
                        .to_string(),
                    span_of_tokens(toks),
                ));
            }

            let node_span = span_of_tokens(toks);
            Ok(WithSpan::new(
                ParsedProofNode::Numbered(ParsedNumberedLine {
                    line_num,
                    depth: *depth,
                    sentence: wff,
                    justification: None,
                    boxed_constant: const_between,
                }),
                node_span,
            ))
        }
        Token::ConseqVertBar(depth) => {
            // we are in the cases 3 or 4
            let rest = &toks[1..];
            // if the line contains only dashes, then its a Fitch Bar
            if rest.iter().all(|t| matches!(t.value(), Token::Dash)) && !rest.is_empty() {
                let span = span_of_tokens(toks);
                Ok(WithSpan::new(
                    ParsedProofNode::FitchBar {
                        depth: *depth,
                    },
                    span,
                ))
            // otherwise its an empty line
            } else if rest.is_empty() {
                Ok(WithSpan::new(
                    ParsedProofNode::Empty {
                        depth: *depth,
                    },
                    first.span().clone(),
                ))
            } else {
                Err(Diagnostic::new(
                    "unnumberd lines can only be empty or can only contain horizontal bars -"
                        .to_string(),
                    span_of_tokens(toks),
                ))
            }
        }
        _ => Err(Diagnostic::new(
            "each text line must start either with a line number or a vertical bar |".to_string(),
            span_of_tokens(toks),
        )),
    }
}

/// Parse a justification, as specified by the grammar defined in the documentation for
/// [parse_proof_line].
fn parse_justification(toks: &[LToken]) -> Result<LJustification, Diagnostic> {
    let justification = parse_justification_tokens(toks)?;
    let span = span_of_tokens(toks);
    Ok(WithSpan::new(justification, span))
}

fn parse_justification_tokens(toks: &[LToken]) -> Result<Justification, Diagnostic> {
    fn token_at(toks: &[LToken], index: usize) -> Option<&WithSpan<Token>> {
        return toks.get(index);
    }

    // We determine the justification (and whether it is syntactically valid) by the first four tokens
    match (token_at(toks, 0),
           token_at(toks, 1),
           token_at(toks, 2),
           token_at(toks, 3)) {
        // "Reit" ":" <num>
        (
            Some(WithSpan{value:Token::Name(name), ..}),
            Some(WithSpan{value:Token::Colon, ..}),
            Some(WithSpan{value:Token::Number(num),span: num_span}),
            None)
            if name == "Reit" => {
            Ok(Justification::Reit(LineRef{span:num_span.clone(),line: *num}))
        }
        // "∧" "Intro" ":" <num> {"," <num>}
        (
            Some(WithSpan{value:Token::And,..}),
            Some(WithSpan{value:Token::Name(name),..}),
            Some(WithSpan{value:Token::Colon,..}),
            Some(WithSpan{value:Token::Number(num),span:num_span})
            )
            if name == "Intro" =>
        {
            let err_str = "failed to parse ∧Intro justification. It should be of this form: ∧Intro:<num>,<num>{,<num>}".to_string();

            let mut nums: Vec<LineRef> = vec![LineRef{span: num_span.clone(), line: *num}];
            let mut i = 4;
            while token_at(toks,i).is_some() {
                if matches!(token_at(toks,i), Some(WithSpan{value: Token::Comma, ..}))  {
                    if let Some(WithSpan{value:Token::Number(next_num), span: next_num_span}) = token_at(toks, i + 1) {
                        nums.push(LineRef{span:next_num_span.clone(), line:*next_num});
                    } else {
                        return Err(Diagnostic::new(err_str, span_of_tokens(toks)));
                    }
                } else {
                    return Err(Diagnostic::new(err_str, span_of_tokens(toks)));
                }
                i += 2;
            }
            return Ok(Justification::AndIntro(nums))
        }
        // "∧" "Elim" ":" <num>
        (
            Some(WithSpan{value:Token::And,..}),
            Some(WithSpan{value: Token::Name(name),..}),
            Some(WithSpan{value: Token::Colon ,..}),
            Some(WithSpan{value: Token::Number(num), span: num_span})
        )    if name == "Elim" =>
        {
            if toks.get(4).is_none() {
                Ok(Justification::AndElim(LineRef{span: num_span.clone(), line:*num}))
            } else {
                return Err(Diagnostic::new("failed to parse ∧Elim justification. It should be of this form: ∧Elim:<num>".to_string(), span_of_tokens(toks)))
            }
        }
        // "∨" "Intro" : <num>
        (
            Some(WithSpan{value:Token::Or,..}),
            Some(WithSpan{value:Token::Name(name), ..}),
            Some(WithSpan{value:Token::Colon,..}),
            Some(WithSpan{value:Token::Number(num), span:num_span })
            ) if name == "Intro" =>
        {
            if toks.get(4).is_none() {
                return Ok(Justification::OrIntro(LineRef{span:num_span.clone(), line:*num}))
            } else {
                return Err(Diagnostic::new("failed to parse ∨Intro justification. It should be of this form: ∨Intro:<num>".to_string(), span_of_tokens(toks)))
            }
        }
        // "∨" "Elim" : <num> , <num>-<num> { , <num>-<num> }
        (
            Some(WithSpan{value:Token::Or, ..}),
            Some(WithSpan{value:Token::Name(name), ..}),
            Some(WithSpan{value: Token::Colon,..}),
            Some(WithSpan{value: Token::Number(num), span: num_span})
        )         if name == "Elim" =>
        {
            let err_str = "failed to parse ∨Elim justification. It should be of this form: ∨Elim:<num>,<num>-<num>{,<num>-<num>}".to_string();
            let mut num_pairs: Vec<(LineRef, LineRef)> = vec![];
            let mut i = 4;
            if toks.get(i).is_none() {
                // should be at least one num-range provided
                return Err(Diagnostic::new(err_str, span_of_tokens(toks)));
            };
            while toks.get(i).is_some() {
                if token_at(toks, i).unwrap().value == Token::Comma {
                    if toks.get(i + 1).is_none()
                        || toks.get(i + 2).is_none()
                        || toks.get(i + 3).is_none()
                    {
                        return Err(Diagnostic::new(err_str, span_of_tokens(toks)));
                    }
                    if let (Some(WithSpan{value:Token::Number(next_num1), span:next_num1_span}), Some(WithSpan{value:Token::Dash,.. }), Some(WithSpan{value:Token::Number(next_num2), span: next_num2_span })) = (
                        token_at(toks, i + 1),
                        token_at(toks, i + 2),
                        token_at(toks, i + 3)
                    ) {
                        num_pairs.push((LineRef{span: next_num1_span.clone(), line:*next_num1}, LineRef{span: next_num2_span.clone(), line: *next_num2 }));
                    } else {
                        return Err(Diagnostic::new(err_str, span_of_tokens(toks)));
                    }
                } else {
                    return Err(Diagnostic::new(err_str, span_of_tokens(toks)));
                }
                i += 4;
            }
            Ok(Justification::OrElim(LineRef{ span: num_span.clone(), line:*num}, num_pairs))
        }
        // → "Intro" : <num>-<num>
        (
            Some(WithSpan{value: Token::Implies, .. }),
            Some(WithSpan{value:Token::Name(name), ..}),
            Some(WithSpan{value:Token::Colon, ..}),
            Some(WithSpan{value:Token::Number(num1), span: num1_span })
        )    if name == "Intro" =>
        {
            let err_str = "failed to parse →Intro justification. It should be of this form: →Intro:<num>-<num>".to_string();
            if toks.len() != 6 {
                return Err(Diagnostic::new(err_str, span_of_tokens(toks)));
            }
            if let (WithSpan{value:Token::Dash,..}, WithSpan{value: Token::Number(num2), span: num2_span}) = (token_at(toks, 4).unwrap(), token_at(toks, 5).unwrap())
            {
                Ok(Justification::ImpliesIntro((LineRef{span: num1_span.clone(), line:*num1}, LineRef{span: num2_span.clone(), line: *num2 })))
            } else {
                return Err(Diagnostic::new(err_str, span_of_tokens(toks)));
            }
        }
        // → "Elim" : <num>, <num>
        (
            Some(WithSpan{value:Token::Implies, ..}),
            Some(WithSpan{value:Token::Name(name), ..}),
            Some(WithSpan{value:Token::Colon, ..}),
            Some(WithSpan{value:Token::Number(num1), span:num1_span})
            ) if name == "Elim" =>
        {
            let err_str =
                "failed to parse →Elim justification. It should be of this form: →Elim:<num>,<num>"
                    .to_string();
            if toks.len() != 6 {
                return Err(Diagnostic::new(err_str, span_of_tokens(toks)));
            }
            if let (WithSpan{value:Token::Comma,..}, WithSpan{value: Token::Number(num2), span:num2_span}) = (token_at(toks, 4).unwrap(), token_at(toks, 5).unwrap())
            {
                return Ok(Justification::ImpliesElim(LineRef{span:num1_span.clone(), line: *num1}, LineRef{ span: num2_span.clone(), line: *num2 }))
            } else {
                return Err(Diagnostic::new(err_str, span_of_tokens(toks)));
            }
        }
        // ↔ "Intro" : <num>-<num>, <num>-<num>
        (
            Some(WithSpan{value:Token::Bicond, ..}),
            Some(WithSpan{value:Token::Name(name) ,..}),
            Some(WithSpan{value: Token::Colon, ..}),
            Some(WithSpan{value: Token::Number(num1), span:num1_span})
            ) if name == "Intro" =>
        {
            let err_str = "failed to parse ↔Intro justification. It should be of this form: ↔Intro:<num>-<num>,<num>-<num>".to_string();
            if toks.len() != 10 {
                return Err(Diagnostic::new(err_str, span_of_tokens(toks)));
            }

            if let (
               WithSpan{value: Token::Dash, ..},
               WithSpan{value: Token::Number(num2), span: num2_span},
                WithSpan{value:Token::Comma,..},
                WithSpan{value:Token::Number(num3), span: num3_span},
                WithSpan{value: Token::Dash, ..},
                WithSpan{value: Token::Number(num4), span: num4_span }) =
                  (token_at(toks, 4).unwrap(), token_at(toks, 5).unwrap(), token_at(toks, 6).unwrap(),
                   token_at(toks, 7).unwrap(), token_at(toks, 8).unwrap(), token_at(toks, 9).unwrap())
            {
                Ok(Justification::BicondIntro(
                        (LineRef{ span: num1_span.clone(), line:*num1}, LineRef{span: num2_span.clone(), line:*num2 }),
                        (LineRef{ span: num3_span.clone(), line:*num3}, LineRef{span: num4_span.clone(), line:*num4 })))
            } else {
                return Err(Diagnostic::new(err_str, span_of_tokens(toks)));
            }
        }
        // ↔ "Elim" : <num>,<num>
        (
            Some(WithSpan {              value: Token::Bicond,                ..            }),
            Some(WithSpan {                value: Token::Name(name),                ..            }),
            Some(WithSpan {                value: Token::Colon,                ..            }),
            Some(WithSpan {value: Token::Number(num1),                span: num1_span,            }),
        ) if name == "Elim" => {
            let err_str =
                "failed to parse ↔Elim justification. It should be of this form: ↔Elim:<num>,<num>"
                    .to_string();

            if toks.len() != 6 {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            } else if let (
                WithSpan {
                    value: Token::Comma,
                    ..
                },
                WithSpan {
                    value: Token::Number(num2),
                    span: num2_span,
                },
            ) = (
                token_at(toks, 4).unwrap(),
                token_at(toks, 5).unwrap(),
            ) {
                Ok(Justification::BicondElim(
                    LineRef {
                        span: num1_span.clone(),
                        line: *num1,
                    },
                    LineRef {
                        span: num2_span.clone(),
                        line: *num2,
                    },
                ))
            } else {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            }
        }

        // ¬ "Intro" : <num>-<num>
        (
            Some(WithSpan {
                value: Token::Not,
                ..
            }),
            Some(WithSpan {
                value: Token::Name(name),
                ..
            }),
            Some(WithSpan {
                value: Token::Colon,
                ..
            }),
            Some(WithSpan {
                value: Token::Number(num1),
                span: num1_span,
            }),
        ) if name == "Intro" => {
            let err_str =
                "failed to parse ¬Intro justification. It should be of this form: ¬Intro:<num>-<num>"
                    .to_string();

            if toks.len() != 6 {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            } else if let (
                WithSpan {
                    value: Token::Dash,
                    ..
                },
                WithSpan {
                    value: Token::Number(num2),
                    span: num2_span,
                },
            ) = (
                token_at(toks, 4).unwrap(),
                token_at(toks, 5).unwrap(),
            ) {
                Ok(Justification::NotIntro((
                    LineRef {
                        span: num1_span.clone(),
                        line: *num1,
                    },
                    LineRef {
                        span: num2_span.clone(),
                        line: *num2,
                    },
                )))
            } else {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            }
        }

        // ¬ "Elim" : <num>
        (
            Some(WithSpan {
                value: Token::Not,
                ..
            }),
            Some(WithSpan {
                value: Token::Name(name),
                ..
            }),
            Some(WithSpan {
                value: Token::Colon,
                ..
            }),
            Some(WithSpan {
                value: Token::Number(num),
                span: num_span,
            }),
        ) if name == "Elim" => {
            let err_str =
                "failed to parse ¬Elim justification. It should be of this form: ¬Elim:<num>"
                    .to_string();

            if token_at(toks, 4).is_none() {
                Ok(Justification::NotElim(LineRef {
                    span: num_span.clone(),
                    line: *num,
                }))
            } else {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            }
        }

        // ⊥ "Intro" : <num>,<num>
        (
            Some(WithSpan {
                value: Token::Bottom,
                ..
            }),
            Some(WithSpan {
                value: Token::Name(name),
                ..
            }),
            Some(WithSpan {
                value: Token::Colon,
                ..
            }),
            Some(WithSpan {
                value: Token::Number(num1),
                span: num1_span,
            }),
        ) if name == "Intro" => {
            let err_str =
                "failed to parse ⊥Intro justification. It should be of this form: ⊥Intro:<num>,<num>"
                    .to_string();

            if toks.len() != 6 {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            } else if let (
                WithSpan {
                    value: Token::Comma,
                    ..
                },
                WithSpan {
                    value: Token::Number(num2),
                    span: num2_span,
                },
            ) = (
                token_at(toks, 4).unwrap(),
                token_at(toks, 5).unwrap(),
            ) {
                Ok(Justification::BottomIntro(
                    LineRef {
                        span: num1_span.clone(),
                        line: *num1,
                    },
                    LineRef {
                        span: num2_span.clone(),
                        line: *num2,
                    },
                ))
            } else {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            }
        }

        // ⊥ "Elim" : <num>
        (
            Some(WithSpan {
                value: Token::Bottom,
                ..
            }),
            Some(WithSpan {
                value: Token::Name(name),
                ..
            }),
            Some(WithSpan {
                value: Token::Colon,
                ..
            }),
            Some(WithSpan {
                value: Token::Number(num),
                span: num_span,
            }),
        ) if name == "Elim" => {
            let err_str =
                "failed to parse ⊥Elim justification. It should be of this form: ⊥Elim:<num>"
                    .to_string();

            if token_at(toks, 4).is_none() {
                Ok(Justification::BottomElim(LineRef {
                    span: num_span.clone(),
                    line: *num,
                }))
            } else {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            }
        }

        // = "Intro"
        (
            Some(WithSpan {
                value: Token::Equals,
                ..
            }),
            Some(WithSpan {
                value: Token::Name(name),
                ..
            }),
            ..
        ) if name == "Intro" => {
            let err_str = "failed to parse =Intro justification. This proof rule goes without colon and without line references, so all you write is just '=Intro'".to_string();

            if toks.len() == 2 {
                Ok(Justification::EqualsIntro)
            } else {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            }
        }

        // = "Elim": <num>,<num>
        (
            Some(WithSpan {
                value: Token::Equals,
                ..
            }),
            Some(WithSpan {
                value: Token::Name(name),
                ..
            }),
            Some(WithSpan {
                value: Token::Colon,
                ..
            }),
            Some(WithSpan {
                value: Token::Number(num1),
                span: num1_span,
            }),
        ) if name == "Elim" => {
            let err_str =
                "failed to parse =Elim justification. It should be of this form: =Elim:<num>,<num>"
                    .to_string();

            if toks.len() != 6 {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            } else if let (
                WithSpan {
                    value: Token::Comma,
                    ..
                },
                WithSpan {
                    value: Token::Number(num2),
                    span: num2_span,
                },
            ) = (
                token_at(toks, 4).unwrap(),
                token_at(toks, 5).unwrap(),
            ) {
                Ok(Justification::EqualsElim(
                    LineRef {
                        span: num1_span.clone(),
                        line: *num1,
                    },
                    LineRef {
                        span: num2_span.clone(),
                        line: *num2,
                    },
                ))
            } else {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            }
        }

        // ∀ "Intro" : <num>-<num>
        (
            Some(WithSpan {
                value: Token::Forall,
                ..
            }),
            Some(WithSpan {
                value: Token::Name(name),
                ..
            }),
            Some(WithSpan {
                value: Token::Colon,
                ..
            }),
            Some(WithSpan {
                value: Token::Number(num1),
                span: num1_span,
            }),
        ) if name == "Intro" => {
            let err_str =
                "failed to parse ∀Intro justification. It should be of this form: ∀Intro:<num>-<num>"
                    .to_string();

            if toks.len() != 6 {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            } else if let (
                WithSpan {
                    value: Token::Dash,
                    ..
                },
                WithSpan {
                    value: Token::Number(num2),
                    span: num2_span,
                },
            ) = (
                token_at(toks, 4).unwrap(),
                token_at(toks, 5).unwrap(),
            ) {
                Ok(Justification::ForallIntro((
                    LineRef {
                        span: num1_span.clone(),
                        line: *num1,
                    },
                    LineRef {
                        span: num2_span.clone(),
                        line: *num2,
                    },
                )))
            } else {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            }
        }

        // ∀ "Elim" : <num>
        (
            Some(WithSpan {
                value: Token::Forall,
                ..
            }),
            Some(WithSpan {
                value: Token::Name(name),
                ..
            }),
            Some(WithSpan {
                value: Token::Colon,
                ..
            }),
            Some(WithSpan {
                value: Token::Number(num),
                span: num_span,
            }),
        ) if name == "Elim" => {
            let err_str =
                "failed to parse ∀Elim justification. It should be of this form: ∀Elim:<num>"
                    .to_string();

            if token_at(toks, 4).is_none() {
                Ok(Justification::ForallElim(LineRef {
                    span: num_span.clone(),
                    line: *num,
                }))
            } else {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            }
        }

        // ∃ "Intro" : <num>
        (
            Some(WithSpan {
                value: Token::Exists,
                ..
            }),
            Some(WithSpan {
                value: Token::Name(name),
                ..
            }),
            Some(WithSpan {
                value: Token::Colon,
                ..
            }),
            Some(WithSpan {
                value: Token::Number(num),
                span: num_span,
            }),
        ) if name == "Intro" => {
            let err_str =
                "failed to parse ∃Intro justification. It should be of this form: ∃Intro:<num>"
                    .to_string();

            if token_at(toks, 4).is_none() {
                Ok(Justification::ExistsIntro(LineRef {
                    span: num_span.clone(),
                    line: *num,
                }))
            } else {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            }
        }

        // ∃ "Elim" : <num>, <num>-<num>
        (
            Some(WithSpan {
                value: Token::Exists,
                ..
            }),
            Some(WithSpan {
                value: Token::Name(name),
                ..
            }),
            Some(WithSpan {
                value: Token::Colon,
                ..
            }),
            Some(WithSpan {
                value: Token::Number(num1),
                span: num1_span,
            }),
        ) if name == "Elim" => {
            let err_str =
                "failed to parse ∃Elim justification. It should be of this form: ∃Elim:<num>,<num>-<num>"
                    .to_string();

            if toks.len() != 8 {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            } else if let (
                WithSpan {
                    value: Token::Comma,
                    ..
                },
                WithSpan {
                    value: Token::Number(num2),
                    span: num2_span,
                },
                WithSpan {
                    value: Token::Dash,
                    ..
                },
                WithSpan {
                    value: Token::Number(num3),
                    span: num3_span,
                },
            ) = (
                token_at(toks, 4).unwrap(),
                token_at(toks, 5).unwrap(),
                token_at(toks, 6).unwrap(),
                token_at(toks, 7).unwrap(),
            ) {
                Ok(Justification::ExistsElim(
                    LineRef {
                        span: num1_span.clone(),
                        line: *num1,
                    },
                    (
                        LineRef {
                            span: num2_span.clone(),
                            line: *num2,
                        },
                        LineRef {
                            span: num3_span.clone(),
                            line: *num3,
                        },
                    ),
                ))
            } else {
                Err(Diagnostic::new(err_str, span_of_tokens(toks)))
            }
        }

        _ => Err(Diagnostic::new(
            "failed to parse justification. Make sure that you have references where necessary, and note that the proper capitalization is 'Intro'/'Elim'/'Reit'."
                .to_string(),
            span_of_tokens(toks),
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proof_lexer_diagnostic_has_physical_span() {
        let diagnostic = parse_fitch_proof("\n1 | P\n2 | P @ Reit:1").unwrap_err();

        assert_eq!(
            diagnostic.span,
            Span::new(Location::new(None, 3, 6), Location::new(None, 3, 7))
        );
        assert_eq!(diagnostic.message, "lexer failure near line 2: invalid character found: @");
        assert_eq!(
            parse_fitch_proof("\n1 | P\n2 | P @ Reit:1").unwrap_err().message,
            diagnostic.message
        );
    }

    #[test]
    fn proof_parser_diagnostic_uses_expression_span() {
        let diagnostic = parse_fitch_proof("\n1 | P(").unwrap_err();

        assert_eq!(
            diagnostic.span,
            Span::new(Location::new(None, 2, 4), Location::new(None, 2, 6))
        );
        assert_eq!(parse_fitch_proof("\n1 | P(").unwrap_err().message, diagnostic.message);
    }

    #[test]
    fn test_lexer_1() {
        assert_eq!(
            lex_tokens("   THIs is SoMe  SiLLY  test  "),
            Ok(vec![
                Token::Name("THIs".to_owned()),
                Token::Name("is".to_owned()),
                Token::Name("SoMe".to_owned()),
                Token::Name("SiLLY".to_owned()),
                Token::Name("test".to_owned())
            ])
        );
    }

    #[test]
    fn test_lexer_2() {
        assert_eq!(
            lex_tokens("   THIs is SoMe  S∀LLY  test  "),
            Ok(vec![
                Token::Name("THIs".to_owned()),
                Token::Name("is".to_owned()),
                Token::Name("SoMe".to_owned()),
                Token::Name("S".to_owned()),
                Token::Forall,
                Token::Name("LLY".to_owned()),
                Token::Name("test".to_owned())
            ])
        );
    }
    #[test]
    fn test_lexer_3() {
        assert_eq!(
            lex_tokens("   THIs is SoMe  S∀ ∀∀LLY  test  "),
            Ok(vec![
                Token::Name("THIs".to_owned()),
                Token::Name("is".to_owned()),
                Token::Name("SoMe".to_owned()),
                Token::Name("S".to_owned()),
                Token::Forall,
                Token::Forall,
                Token::Forall,
                Token::Name("LLY".to_owned()),
                Token::Name("test".to_owned())
            ])
        );
    }
    #[test]
    fn test_lexer_4() {
        assert_eq!(
            lex_tokens("∀x(P(x,a)→P(a,x))∨ (A∧ ItIsSunny∧¬∃y P(y,y))∨a=c"),
            Ok(vec![
                Token::Forall,
                Token::Name("x".to_owned()),
                Token::LPar,
                Token::Name("P".to_owned()),
                Token::LPar,
                Token::Name("x".to_owned()),
                Token::Comma,
                Token::Name("a".to_owned()),
                Token::RPar,
                Token::Implies,
                Token::Name("P".to_owned()),
                Token::LPar,
                Token::Name("a".to_owned()),
                Token::Comma,
                Token::Name("x".to_owned()),
                Token::RPar,
                Token::RPar,
                Token::Or,
                Token::LPar,
                Token::Name("A".to_owned()),
                Token::And,
                Token::Name("ItIsSunny".to_owned()),
                Token::And,
                Token::Not,
                Token::Exists,
                Token::Name("y".to_owned()),
                Token::Name("P".to_owned()),
                Token::LPar,
                Token::Name("y".to_owned()),
                Token::Comma,
                Token::Name("y".to_owned()),
                Token::RPar,
                Token::RPar,
                Token::Or,
                Token::Name("a".to_owned()),
                Token::Equals,
                Token::Name("c".to_owned()),
            ])
        );
    }

    fn lex_tokens(input: &str) -> Result<Vec<Token>, String> {
        lex(input)
            .map(|toks| toks.into_iter().map(|t| t.value().clone()).collect())
            .map_err(|d| d.message)
    }

    fn lwff(wff: Wff) -> LWff {
        WithSpan::dummy(wff)
    }

    fn lterm(term: Term) -> LTerm {
        WithSpan::dummy(term)
    }

    fn strip_term_spans(term: LTerm) -> LTerm {
        let WithSpan {
            value,
            ..
        } = term;
        let value = match value {
            Term::Atomic(name) => Term::Atomic(name),
            Term::FuncApp(name, args) => {
                Term::FuncApp(name, args.into_iter().map(strip_term_spans).collect())
            }
        };
        WithSpan::dummy(value)
    }

    fn strip_wff_spans(wff: LWff) -> LWff {
        let WithSpan {
            value,
            ..
        } = wff;
        let sanitized = match value {
            Wff::And(children) => Wff::And(children.into_iter().map(strip_wff_spans).collect()),
            Wff::Or(children) => Wff::Or(children.into_iter().map(strip_wff_spans).collect()),
            Wff::Implies(lhs, rhs) => {
                Wff::Implies(Box::new(strip_wff_spans(*lhs)), Box::new(strip_wff_spans(*rhs)))
            }
            Wff::Bicond(lhs, rhs) => {
                Wff::Bicond(Box::new(strip_wff_spans(*lhs)), Box::new(strip_wff_spans(*rhs)))
            }
            Wff::Not(inner) => Wff::Not(Box::new(strip_wff_spans(*inner))),
            Wff::Bottom => Wff::Bottom,
            Wff::Forall(var, body) => Wff::Forall(var, Box::new(strip_wff_spans(*body))),
            Wff::Exists(var, body) => Wff::Exists(var, Box::new(strip_wff_spans(*body))),
            Wff::Atomic(name) => Wff::Atomic(name),
            Wff::PredApp(name, terms) => {
                Wff::PredApp(name, terms.into_iter().map(strip_term_spans).collect())
            }
            Wff::Equals(lhs, rhs) => Wff::Equals(strip_term_spans(lhs), strip_term_spans(rhs)),
        };
        WithSpan::dummy(sanitized)
    }

    fn parse_expr(expr: &str) -> Option<LWff> {
        parse_logical_expression_string(expr).map(strip_wff_spans)
    }

    #[allow(dead_code)]
    fn func(name: &str, args: Vec<Term>) -> Term {
        Term::FuncApp(name.to_string(), args.into_iter().map(lterm).collect())
    }

    fn atom(name: &str) -> LWff {
        lwff(Wff::Atomic(name.to_string()))
    }

    fn and(children: Vec<LWff>) -> LWff {
        lwff(Wff::And(children))
    }

    fn or(children: Vec<LWff>) -> LWff {
        lwff(Wff::Or(children))
    }

    fn implies(lhs: LWff, rhs: LWff) -> LWff {
        lwff(Wff::Implies(Box::new(lhs), Box::new(rhs)))
    }

    fn forall(var: &str, body: LWff) -> LWff {
        lwff(Wff::Forall(var.to_string(), Box::new(body)))
    }

    fn pred(name: &str, args: Vec<Term>) -> LWff {
        lwff(Wff::PredApp(name.to_string(), args.into_iter().map(lterm).collect()))
    }

    fn eq_terms(left: Term, right: Term) -> LWff {
        lwff(Wff::Equals(lterm(left), lterm(right)))
    }

    fn parse_justification_text(input: &str) -> Result<Justification, Diagnostic> {
        parse_justification(&lex(input).unwrap()).map(|j| j.value().clone())
    }

    #[test]
    fn test_parser_1() {
        assert_eq!(parse_expr("A∧B"), Some(and(vec![atom("A"), atom("B")])));
    }
    #[test]
    fn test_parser_2() {
        assert_eq!(parse_expr("AB"), Some(atom("AB")));
    }
    #[test]
    fn test_parser_3() {
        assert_eq!(parse_expr("a∧B"), None);
    }
    #[test]
    fn test_parser_4() {
        assert_eq!(parse_expr("aAAA"), None);
    }
    #[test]
    fn test_parser_5() {
        assert_eq!(parse_expr("A∨B"), Some(or(vec![atom("A"), atom("B")])));
    }
    #[test]
    fn test_parser_6() {
        assert_eq!(parse_expr("A∨∧B"), None);
    }
    #[test]
    fn test_parser_7() {
        assert_eq!(parse_expr("A→B"), Some(implies(atom("A"), atom("B"))));
    }
    #[test]
    fn test_parser_8() {
        assert_eq!(parse_expr("A→→→B"), None);
    }
    #[test]
    fn test_parser_9() {
        assert_eq!(
            parse_expr("∀x(∀y P(x,y))"),
            Some(forall(
                "x",
                forall("y", pred("P", vec![Term::Atomic("x".into()), Term::Atomic("y".into())]))
            ))
        );
        assert_eq!(parse_expr("∀x(∀y P(x,y))"), parse_expr("∀x∀y P(x,y)"));
        assert_eq!(parse_expr("∀x(∀y P(x,y))"), parse_expr("(∀x∀y P(x,y))"));
    }
    #[test]
    fn test_parser_10() {
        assert_eq!(parse_expr("∀(x∀y P(x,y))"), None);
    }
    #[test]
    fn test_parser_11() {
        let expr1 = "∀x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y)))";
        let expected_result = parse_expr(expr1);

        // correct

        // correct, same as expr1 but with a lot of spaces
        let expr2 = " ∀ x ( P ( a , b , x )   → Q ( f ( a ) , f ( b , c , d ) , g ( x ) ) ) ∨ f ( a , b ) = f ( bla , c ) ∨ ¬ ∃ x ¬ ¬ ¬ ∃ y ¬ ¬ ∀ z ¬ ¬ ( P ( f ( x ) , f ( y ) , f ( z ) ) → ¬ ( A ( x ) ∧ B ( y ) ) ) ";

        // wrong, misses a bracket in the end
        let expr3 = "∀x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y))";

        // correct, same as expr1 but with a lot of extra brackets
        let expr4 = "((∀x((P(a,b,x))→((Q(f(a),f(b,c,d),g(x)))))∨((((((f(a,b)=f(bla,c)))))))∨(¬(∃x(¬(¬(¬(∃y(¬(¬(∀z(¬(¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y))))))))))))))))";

        // wrong, same as expr1 but with brackets in a place where they shouldn't be
        let expr5 = "∀x(P((a),b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y)))";

        // wrong, same as expr1 but with brackets in a place where they shouldn't be
        let expr6 = "∀x(P((a,b,x))→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y)))";

        // wrong, same as expr1 but with brackets in a place where they shouldn't be
        let expr7 = "∀x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃(x)¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y)))";

        // wrong, same as expr1 but with one ) removed
        let expr8 = "∀x(P(a,b,x→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))→¬(A(x)∧B(y)))";

        // wrong, same as expr1 but with one → removed
        let expr9 = "∀x(P(a,b,x)→Q(f(a),f(b,c,d),g(x)))∨f(a,b)=f(bla,c)∨¬∃x¬¬¬∃y¬¬∀z¬¬(P(f(x),f(y),f(z))¬(A(x)∧B(y)))";

        assert_eq!(parse_expr(expr1), expected_result);
        assert_eq!(parse_expr(expr2), expected_result);
        assert_eq!(parse_expr(expr3), None);
        assert_eq!(parse_expr(expr4), expected_result);
        assert_eq!(parse_expr(expr5), None);
        assert_eq!(parse_expr(expr6), None);
        assert_eq!(parse_expr(expr7), None);
        assert_eq!(parse_expr(expr8), None);
        assert_eq!(parse_expr(expr9), None);
    }
    #[test]
    fn test_parser_12() {
        assert_eq!(parse_expr("A∨B∧C"), None);
    }
    #[test]
    fn test_parser_13() {
        assert_eq!(parse_expr("A∧B∨B"), None);
    }
    #[test]
    fn test_parser_14() {
        assert_eq!(parse_expr("a=b=b"), None);
    }
    #[test]
    fn test_parser_15() {
        assert_eq!(
            parse_expr("a=b"),
            Some(eq_terms(Term::Atomic("a".to_string()), Term::Atomic("b".to_string())))
        );
    }

    /*
        TODO: fix spans

        #[test]
        fn test_justification_parser_or_elim() {
            assert_eq!(
                parse_justification_text("∨Elim:42,43-44"),
                Ok(Justification::OrElim(42, vec![(43, 44)]))
            );
            assert_eq!(
                parse_justification_text("∨Elim:42,43-44,45-46,47-48"),
                Ok(Justification::OrElim(42, vec![(43, 44), (45, 46), (47, 48)]))
            );
            assert!(parse_justification_text("∨Elim:42,43-44,45-46,47,48").is_err());
            assert!(parse_justification_text("∨Elim:42,43-44,45-46-47-48").is_err());
            assert!(parse_justification_text("∨Elim:42-43-44,45-46,47-48").is_err());
            assert!(parse_justification_text("∨Elim-42,43-44,45-46,47-48").is_err());
            assert!(parse_justification_text("∨Elim:42,43-44,45-46,47-48,").is_err());
            assert!(parse_justification_text("∨Elim:42,43-44,45-46,47-48,49").is_err());
            assert!(parse_justification_text("∨Elim:42,43-44,45-46,47-48,49-").is_err());
            assert!(parse_justification_text("∨Elim:42").is_err());
        }
        #[test]
        fn test_justification_parser_and_intro() {
            assert_eq!(
                parse_justification_text("∧Intro:42,43,44"),
                Ok(Justification::AndIntro(vec![42, 43, 44]))
            );
            assert_eq!(
                parse_justification_text("∧Intro:42,43"),
                Ok(Justification::AndIntro(vec![42, 43]))
            );
            assert_eq!(
                parse_justification_text("∧Intro:42"),
                // TODO: decide whether i want to keep behavior like this (a "unary conjunction")
                Ok(Justification::AndIntro(vec![42]))
            );
            assert!((parse_justification_text("∧Intro:42-43").is_err()));
            assert!((parse_justification_text("∧Intro:").is_err()));
        }
        #[test]
        fn test_justification_parser_exists_elim() {
            assert_eq!(
                parse_justification_text("∃Elim:42,43-44"),
                Ok(Justification::ExistsElim(42, (43, 44)))
            );
        }
        #[test]
        fn test_justification_parser_implies_elim() {
            assert_eq!(parse_justification_text("→Elim:42,43"), Ok(Justification::ImpliesElim(42, 43)));
            assert!((parse_justification_text("→Elim:42,43,").is_err()));
        }
    */
    #[test]
    fn test_parser_bug_infinite_loop_1() {
        let toks = lex("(f(g(a),=b)").unwrap();
        let _ = parse_e2(&toks);
    }

    #[test]
    fn test_parser_bug_infinite_loop_2() {
        let toks = lex("f(g(a),=b").unwrap();
        let _ = parse_e1(&toks);
    }
    #[test]
    fn test_parser_bug_infinite_loop_3() {
        let toks = lex("f(g(a),=b").unwrap();
        let _ = parse_term(&toks);
    }
    #[test]
    fn test_parser_bug_infinite_loop_4() {
        let toks = lex("(g(a),=b").unwrap();
        let _ = parse_arg_list(&toks);
    }
}
