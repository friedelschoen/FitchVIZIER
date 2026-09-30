use std::fmt;
use std::hash::{Hash, Hasher};

/// Location metadata for syntactic elements originating from parsed input.
#[derive(Debug, Clone, PartialEq, Eq, Default, Hash)]
pub struct Location {
    pub file: Option<String>,
    pub line: usize,
    pub column: usize,
}

impl Location {
    pub fn new(file: Option<String>, line: usize, column: usize) -> Self {
        Self {
            file,
            line,
            column,
        }
    }

    pub fn dummy() -> Self {
        Self {
            file: None,
            line: 0,
            column: 0,
        }
    }

    pub fn next_line(&mut self) {
        self.line += 1;
        self.column = 1;
    }

    pub fn next_column(&mut self) {
        self.column += 1;
    }

    pub fn advance_by(&mut self, n: usize) {
        self.column += n;
    }
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(file) = &self.file {
            write!(f, "{}:{}:{}", file, self.line, self.column)
        } else {
            write!(f, "{}:{}", self.line, self.column)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: Location,
    pub end: Location,
}

impl Span {
    pub fn new(start: Location, end: Location) -> Self {
        Self {
            start,
            end,
        }
    }

    pub fn point(location: Location) -> Self {
        let mut end = location.clone();
        end.next_column();

        Self {
            start: location,
            end,
        }
    }

    pub fn cover(first: &Span, last: &Span) -> Self {
        Self {
            start: first.start.clone(),
            end: last.end.clone(),
        }
    }

    pub fn dummy() -> Self {
        Self {
            start: Location::dummy(),
            end: Location::dummy(),
        }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Span({} -> {})", self.start, self.end)
    }
}

/// A value paired with location metadata.
#[derive(Debug, Clone)]
pub struct WithSpan<T> {
    pub value: T,
    pub span: Span,
}

impl<T> WithSpan<T> {
    pub fn new(value: T, span: Span) -> Self {
        Self {
            value,
            span,
        }
    }

    pub fn dummy(value: T) -> Self {
        Self {
            value,
            span: Span::dummy(),
        }
    }

    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> WithSpan<U> {
        WithSpan {
            value: f(self.value),
            span: self.span,
        }
    }

    pub fn map_ref<U>(&self, f: impl FnOnce(&T) -> U) -> WithSpan<U> {
        WithSpan {
            value: f(&self.value),
            span: self.span.clone(),
        }
    }

    pub fn as_ref(&self) -> WithSpan<&T> {
        WithSpan {
            value: &self.value,
            span: self.span.clone(),
        }
    }

    pub fn take_value(self) -> T {
        self.value
    }

    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn value(&self) -> &T {
        &self.value
    }

    pub fn value_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

impl<T: PartialEq> PartialEq for WithSpan<T> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}

impl<T: Eq> Eq for WithSpan<T> {}

impl<T: Default> Default for WithSpan<T> {
    fn default() -> Self {
        Self::dummy(T::default())
    }
}

impl<T: Hash> Hash for WithSpan<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

impl<T: fmt::Debug> fmt::Display for WithSpan<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} @ {}", self.value, self.span)
    }
}

// the following two methoCs allow us to coerce &WithLoc<T> into &T for convenience
impl<T> std::ops::Deref for WithSpan<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T> std::ops::DerefMut for WithSpan<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}
