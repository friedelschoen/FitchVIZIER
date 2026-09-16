use crate::loc::{Span, WithSpan};

pub type LProofNode = WithSpan<ProofNode>;
pub type LWff = WithSpan<Wff>;
pub type LTerm = WithSpan<Term>;
pub type LJustification = WithSpan<Justification>;

// Temp code for plugging in type errors
#[allow(dead_code)]
pub fn dummy_lwff(wff: Wff) -> LWff {
    WithSpan::dummy(wff)
}

#[allow(dead_code)]
pub fn dummy_lterm(term: Term) -> LTerm {
    WithSpan::dummy(term)
}

#[allow(dead_code)]
pub fn dummy_ljustification(just: Justification) -> LJustification {
    WithSpan::dummy(just)
}

#[allow(dead_code)]
pub fn boxed_lwff(wff: Wff) -> Box<LWff> {
    Box::new(dummy_lwff(wff))
}

#[allow(dead_code)]
pub fn vec_lwff(wffs: Vec<Wff>) -> Vec<LWff> {
    wffs.into_iter().map(dummy_lwff).collect()
}

#[allow(dead_code)]
pub fn vec_lterm(terms: Vec<Term>) -> Vec<LTerm> {
    terms.into_iter().map(dummy_lterm).collect()
}

/// A `ProofNode` represents every relevant element of a Fitch-style proof in document order.
///
/// Roughly, it correponds to either a physical line in a text-based
/// proof, or it represens opening/closing a new subproof.
#[derive(PartialEq, Debug, Clone)]
pub enum ProofNode {
    /// A numbered line (premise or inference). These are the only nodes that carry a line number.
    Numbered(NumberedLine),
    /// A Fitch bar line (`| ---`) separating premises from a subproof body or the initial derivation.
    FitchBar { depth: usize },
    /// An empty line that contains only scope markers (vertical bars). These are rare but allowed.
    Empty { depth: usize },
    /// Synthetic element inserted when a new subproof scope is opened. It immediately precedes the
    /// numbered line that serves as the subproof premise.
    SubproofOpen { depth: usize },
    /// Synthetic element inserted when one or more subproof scopes close. It precedes the next
    /// textual node at the shallower depth.
    SubproofClose { depth: usize },
}

impl ProofNode {
    pub fn depth(&self) -> usize {
        match self {
            ProofNode::Numbered(line) => line.depth,
            ProofNode::FitchBar { depth }
            | ProofNode::Empty { depth }
            | ProofNode::SubproofOpen { depth }
            | ProofNode::SubproofClose { depth } => *depth,
        }
    }

    pub fn as_numbered(&self) -> Option<&NumberedLine> {
        if let ProofNode::Numbered(line) = self {
            Some(line)
        } else {
            None
        }
    }

    pub fn line_num(&self) -> Option<usize> {
        return self.as_numbered().map(|s| s.line_num);
    }
    pub fn is_fitch_bar(&self) -> bool {
        matches!(self, ProofNode::FitchBar { .. })
    }

    pub fn is_structural(&self) -> bool {
        matches!(
            self,
            ProofNode::SubproofOpen { .. } | ProofNode::SubproofClose { .. }
        )
    }
}

/// Numbered proof lines carry the logical content of the user's proof.
///
/// A numbered line may be a premise (no justification), an inference
/// (justification present), or a placeholder line where the user has
/// not yet written the justification -- we want to be able to deal
/// with those since we want to provide feedback on imcomplete proofs.
/// Additionaly, when a boxed constant is introduced, it is stored in
/// `boxed_constant`.
#[derive(PartialEq, Debug, Clone)]
pub struct NumberedLine {
    pub line_num: usize,
    pub depth: usize,
    pub sentence: Option<LWff>,
    pub justification: Option<LJustification>,
    pub boxed_constant: Option<LTerm>,
}

#[derive(PartialEq, Debug, Clone)]
/// A logical sentence. "Wff" stands for "well-formed formula", but this is a slightly incorrect
/// name, since for example, a logical sentence that has predicate ariy mismatches is still
/// expressable in this [Wff]. A [Wff] is a core element of a proof. For example, each proof line
/// that has a line number, will contain a [Wff] (unless it is a line which only introduces a boxed
/// constant).
pub enum Wff {
    /// Conjunction.
    And(Vec<LWff>),
    /// Disjunction.
    Or(Vec<LWff>),
    /// Implication.
    Implies(Box<LWff>, Box<LWff>),
    /// Biconditional.
    Bicond(Box<LWff>, Box<LWff>),
    /// Negation.
    Not(Box<LWff>),
    /// Bottom / contradiction.
    Bottom,
    /// Universal quantification.
    ///
    /// The associated [String] denotes the name of the variable that is quantified over, and the
    /// associated [Wff] is the rest of the sentence.
    Forall(String, Box<LWff>),
    /// Existential quantification.
    ///
    /// The associated [String] denotes the name of the variable that is quantified over, and the
    /// associated [Wff] is the rest of the sentence.
    Exists(String, Box<LWff>),
    /// This is a nullary predicate, for example "P".
    Atomic(String),
    /// This is n-ary predicate application, for n >= 1.
    ///
    /// For example, if you have the predicate application `P(x,y,f(a))`, then the associated [String]
    /// would be "P" and the associated vector of [Term]s would correspond to `x`, `y` and `f(a)`,
    /// respectively.
    PredApp(String, Vec<LTerm>),
    /// The equality predicate, applied to two [Term]s.
    Equals(LTerm, LTerm),
}

/// This a logical term. A term can be either a constant, a variable, or a function application
/// (which is a function applied to a positive number of terms).
#[derive(PartialEq, Debug, Clone, Hash, Eq)]
pub enum Term {
    /// A variable or constant.
    Atomic(String),
    // Function application
    FuncApp(String, Vec<LTerm>),
}

#[derive(PartialEq, Debug, Clone, Hash, Eq)]
pub struct LineRef {
    pub line: usize,
    pub span: Span,
}

impl std::fmt::Display for LineRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.line)
    }
}

/// This enum represents the justification rules for an inference. The associated [usize]s denote
/// the line numbers being represented.
#[derive(PartialEq, Debug, Clone)]
pub enum Justification {
    AndIntro(Vec<LineRef>),
    AndElim(LineRef),
    OrIntro(LineRef),
    OrElim(LineRef, Vec<(LineRef, LineRef)>),
    NotIntro((LineRef, LineRef)),
    NotElim(LineRef),
    BottomIntro(LineRef, LineRef),
    BottomElim(LineRef),
    ImpliesIntro((LineRef, LineRef)),
    ImpliesElim(LineRef, LineRef),
    BicondIntro((LineRef, LineRef), (LineRef, LineRef)),
    BicondElim(LineRef, LineRef),
    EqualsIntro,
    EqualsElim(LineRef, LineRef),
    ForallIntro((LineRef, LineRef)),
    ForallElim(LineRef),
    ExistsIntro(LineRef),
    ExistsElim(LineRef, (LineRef, LineRef)),
    Reit(LineRef),
}

impl NumberedLine {
    pub fn introduces_boxed_constant(&self) -> bool {
        self.boxed_constant.is_some()
    }

    pub fn is_inference(&self) -> bool {
        self.justification.is_some()
    }

    pub fn sentence(&self) -> Option<&Wff> {
        self.sentence.as_ref().map(|w| w.value())
    }

    pub fn sentence_with_loc(&self) -> Option<&LWff> {
        self.sentence.as_ref()
    }

    pub fn justification(&self) -> Option<&Justification> {
        self.justification.as_ref().map(|j| j.value())
    }

    pub fn justification_with_loc(&self) -> Option<&LJustification> {
        self.justification.as_ref()
    }

    pub fn boxed_constant(&self) -> Option<&Term> {
        self.boxed_constant.as_ref().map(|t| t.value())
    }

    pub fn boxed_constant_with_loc(&self) -> Option<&LTerm> {
        self.boxed_constant.as_ref()
    }

    pub fn sentence_span(&self) -> Option<&Span> {
        self.sentence.as_ref().map(|w| w.span())
    }

    pub fn justification_span(&self) -> Option<&Span> {
        self.justification.as_ref().map(|j| j.span())
    }

    pub fn boxed_constant_span(&self) -> Option<&Span> {
        self.boxed_constant.as_ref().map(|t| t.span())
    }

    pub fn sentence_owned(&self) -> Option<Wff> {
        self.sentence().cloned()
    }

    pub fn justification_owned(&self) -> Option<Justification> {
        self.justification().cloned()
    }

    pub fn boxed_constant_owned(&self) -> Option<Term> {
        self.boxed_constant().cloned()
    }
}

impl Justification {
    pub fn rule_used(self: &Justification) -> (&'static str, &'static str) {
        match self {
            Justification::AndIntro(_) => ("∧", "Intro"),
            Justification::AndElim(_) => ("∧", "Elim"),
            Justification::OrIntro(_) => ("∨", "Intro"),
            Justification::OrElim(_, _) => ("∨", "Elim"),
            Justification::NotIntro(_) => ("¬", "Intro"),
            Justification::NotElim(_) => ("¬", "Elim"),
            Justification::BottomIntro(_, _) => ("⊥", "Intro"),
            Justification::BottomElim(_) => ("⊥", "Elim"),
            Justification::ImpliesIntro(_) => ("→", "Intro"),
            Justification::ImpliesElim(_, _) => ("→", "Elim"),
            Justification::BicondIntro(_, _) => ("↔", "Intro"),
            Justification::BicondElim(_, _) => ("↔", "Elim"),
            Justification::EqualsIntro => ("=", "Intro"),
            Justification::EqualsElim(_, _) => ("=", "Elim"),
            Justification::ForallIntro(_) => ("∀", "Intro"),
            Justification::ForallElim(_) => ("∀", "Elim"),
            Justification::ExistsIntro(_) => ("∃", "Intro"),
            Justification::ExistsElim(_, _) => ("∃", "Elim"),
            Justification::Reit(_) => ("R", "Reit"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticRelation {
    pub message: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub message: String,
    pub span: Option<Span>,
    pub related: Vec<DiagnosticRelation>,
}

impl AsRef<str> for Diagnostic {
    fn as_ref(&self) -> &str {
        &self.message
    }
}

impl Diagnostic {
    pub fn new(message: impl Into<String>, span: Option<Span>) -> Self {
        Self {
            message: message.into(),
            span,
            related: Vec::new(),
        }
    }

    pub fn format(self: &Diagnostic) -> String {
        match &self.span {
            None => self.message.clone(),
            Some(loc) => {
                format!(
                    "{}:{}:{}-{}: {}",
                    loc.start.file.clone().unwrap_or("??".to_string()),
                    loc.start.line,
                    loc.start.column,
                    loc.end.column,
                    self.message
                )
            }
        }
    }

    pub fn with_relation(mut self, message: impl Into<String>, span: Span) -> Self {
        self.related.push(DiagnosticRelation {
            message: message.into(),
            span,
        });
        self
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofResult {
    /// No mistakes; proof is correct.
    Correct(Span),
    /// An 'error' is a mistake that makes the proof wrong, but still allows
    /// the checker to go on and find other mistakes. This [ProofResult::Error]
    /// variant denotes the list of errors that was obtained during analysis.
    Error(Vec<Diagnostic>),
    /// A mistake that is so severe that the checker cannot continue its analysis.
    /// When a fatal error occurs, this fatal error will be returned to the user,
    /// with no other error messages along it.
    ///
    /// Note that when the user checks some proof that should match to some proof template,
    /// a [ProofResult::FatalError] will be returned if the proof does
    /// not match the template.
    FatalError(Diagnostic),
}
