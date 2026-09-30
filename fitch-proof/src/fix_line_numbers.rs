use crate::{data::*, WithSpan};
use std::collections::HashMap;

/// This function 'fixes' the line numbers in a vector of [ProofNode]s.
///
/// If the line numbers already start at 1 and increase by one at a time, then this function does
/// nothing. However, this function does do something in case the line numbers are not properly
/// starting at 1 and increasing by one at a time. This function modifies the numbered lines such
/// that the line numbers will start at 1 and increase by one at a time.
///
/// This function also updates the justifications with the new line numbers, so those do not get
/// messed up. This can be very useful if you have a big proof and you want to delete one unused
/// line in the middle, or if you want to insert a line in the middle. If you want to insert a line
/// in the middle of a big proof, just give that line the line number 1000 (or any unused value)
/// and then apply this function. It will fix all the line numbers and justifications.
///
/// If the proof contains justifications which have line numbers that do not exist in the proof,
/// these line numbers will be set to zero in the justification.
pub fn fix_line_numbers(proof_nodes: &[LParsedProofNode]) -> Result<Vec<LProofNode>, Diagnostic> {
    let mut line_num_map = HashMap::new();
    let mut next_line = 1usize;

    proof_nodes
        .iter()
        .map(|node| -> Result<LProofNode, Diagnostic> {
            let value = match node.value() {
                ParsedProofNode::Numbered(line) => {
                    ProofNode::Numbered(map_numbered_line(&mut line_num_map, &mut next_line, line)?)
                }

                ParsedProofNode::FitchBar {
                    depth,
                } => ProofNode::FitchBar {
                    depth: *depth,
                },

                ParsedProofNode::Empty {
                    depth,
                } => ProofNode::Empty {
                    depth: *depth,
                },

                ParsedProofNode::SubproofOpen {
                    depth,
                } => ProofNode::SubproofOpen {
                    depth: *depth,
                },

                ParsedProofNode::SubproofClose {
                    depth,
                } => ProofNode::SubproofClose {
                    depth: *depth,
                },
            };

            Ok(WithSpan::new(value, node.span.clone()))
        })
        .collect()
}

fn map_numbered_line(
    mapping: &mut HashMap<usize, usize>,
    next_line: &mut usize,
    original: &ParsedNumberedLine,
) -> Result<NumberedLine, Diagnostic> {
    let line_num = *next_line;

    if let WithSpan {
        value: LineNumber::Explicit(old),
        span,
    } = &original.line_num
    {
        if mapping.contains_key(old) {
            return Err(Diagnostic::new(format!("cannot map line {old} twice"), span.clone()));
        }
        mapping.insert(*old, line_num);
    }

    *next_line += 1;

    Ok(NumberedLine {
        line_num,

        justification: original
            .justification
            .as_ref()
            .map(|just| remap_justification(just, mapping)),

        depth: original.depth,
        sentence: original.sentence.clone(),
        boxed_constant: original.boxed_constant.clone(),
    })
}

fn remap_line_ref(mapping: &HashMap<usize, usize>, line_ref: &LineRef) -> LineRef {
    LineRef {
        span: line_ref.span.clone(),

        line: mapping
            .get(&line_ref.line)
            .copied()
            .unwrap_or_else(|| guess_just(mapping, line_ref.line)),
    }
}

fn guess_just(mapping: &HashMap<usize, usize>, line: usize) -> usize {
    for previous in (1..line).rev() {
        if let Some(&mapped) = mapping.get(&previous) {
            return mapped + (line - previous);
        }
    }

    line
}

fn remap_justification(
    just: &WithSpan<Justification>,
    mapping: &HashMap<usize, usize>,
) -> WithSpan<Justification> {
    let remap = |line_ref: &LineRef| remap_line_ref(mapping, line_ref);

    let value = match just.value() {
        Justification::Reit(n) => Justification::Reit(remap(n)),

        Justification::AndIntro(ns) => Justification::AndIntro(ns.iter().map(remap).collect()),

        Justification::AndElim(n) => Justification::AndElim(remap(n)),

        Justification::OrIntro(n) => Justification::OrIntro(remap(n)),

        Justification::OrElim(n, subs) => Justification::OrElim(
            remap(n),
            subs.iter().map(|(a, b)| (remap(a), remap(b))).collect(),
        ),

        Justification::EqualsIntro => Justification::EqualsIntro,

        Justification::EqualsElim(n, m) => Justification::EqualsElim(remap(n), remap(m)),

        Justification::NotIntro((n, m)) => Justification::NotIntro((remap(n), remap(m))),

        Justification::NotElim(n) => Justification::NotElim(remap(n)),

        Justification::BottomIntro(n, m) => Justification::BottomIntro(remap(n), remap(m)),

        Justification::BottomElim(n) => Justification::BottomElim(remap(n)),

        Justification::BicondIntro((a, b), (c, d)) => {
            Justification::BicondIntro((remap(a), remap(b)), (remap(c), remap(d)))
        }

        Justification::BicondElim(n, m) => Justification::BicondElim(remap(n), remap(m)),

        Justification::ForallIntro((a, b)) => Justification::ForallIntro((remap(a), remap(b))),

        Justification::ForallElim(n) => Justification::ForallElim(remap(n)),

        Justification::ExistsIntro(n) => Justification::ExistsIntro(remap(n)),

        Justification::ExistsElim(n, (a, b)) => {
            Justification::ExistsElim(remap(n), (remap(a), remap(b)))
        }

        Justification::ImpliesIntro((n, m)) => Justification::ImpliesIntro((remap(n), remap(m))),

        Justification::ImpliesElim(n, m) => Justification::ImpliesElim(remap(n), remap(m)),
    };

    WithSpan::new(value, just.span.clone())
}
