#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// A constant string, starts with a lowercase letter
    Atom(String),
    /// A constant integer
    Number(i64),
    /// A variable, starting with an uppercase letter
    Variable(String),
    /// A compound term with a functor and argument list
    Compound { functor: String, args: Vec<Term> },
}

impl Term {
    pub fn atom<T: Into<String>>(name: T) -> Self {
        Term::Atom(name.into())
    }

    pub fn number(num: i64) -> Self {
        Term::Number(num)
    }

    pub fn var<T: Into<String>>(name: T) -> Self {
        Term::Variable(name.into())
    }

    pub fn compound<T: Into<String>>(functor: T, args: Vec<Term>) -> Self {
        Term::Compound {
            functor: functor.into(),
            args,
        }
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::Atom(str) | Term::Variable(str) => write!(f, "{}", str),
            Term::Number(num) => write!(f, "{}", num),
            Term::Compound { functor, args } => {
                write!(f, "{}(", functor)?;

                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }

                    write!(f, "{}", arg)?;
                }

                write!(f, ")")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Clause {
    pub head: Term,
    pub body: Vec<Term>,
}

impl Clause {
    pub fn fact(head: Term) -> Self {
        Clause { head, body: vec![] }
    }

    pub fn rule(head: Term, body: Vec<Term>) -> Self {
        Clause { head, body }
    }
}

impl std::fmt::Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.head)?;

        if !self.body.is_empty() {
            write!(f, " :- ")?;

            for (i, term) in self.body.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }

                write!(f, "{}", term)?;
            }
        }

        write!(f, ".")
    }
}
