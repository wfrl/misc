
use std::{rc::Rc, cell::{Cell, RefCell}};
use std::collections::HashMap;
use crate::bstr::Bstr;

#[cfg(test)]
#[path = "tests_kernel.rs"]
mod tests_kernel;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorKind {Syntax, Type, Logic}

#[derive(Debug)]
pub struct ErrorRecord {
    pub kind: ErrorKind,
    pub line: usize,
    pub info: String
}

type Error = Box<ErrorRecord>;

fn syntax_error(line: usize, info: String) -> Error {
    Box::new(ErrorRecord {kind: ErrorKind::Syntax, line, info})
}

fn type_error(line: usize, info: String) -> Error {
    Box::new(ErrorRecord {kind: ErrorKind::Type, line, info})
}

fn logic_error(line: usize, info: String) -> Error {
    Box::new(ErrorRecord {kind: ErrorKind::Logic, line, info})
}

#[derive(Debug)]
enum TokenValue {
    Number(Bstr),
    Identifier(Bstr),
    Symbol(Bstr),
    None
}

struct Token {
    line: usize,
    value: TokenValue
}

impl Token {
    fn is_symbol(&self, b: &str) -> bool {
        match &self.value {
            TokenValue::Symbol(a) => a.as_slice() == b.as_bytes(),
            _ => false
        }
    }
}

impl std::fmt::Debug for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Token {line, value} = self;
        write!(f, "{}:{:?}", line, value)
    }
}

fn in_sym2(s: &[u8], i: usize, n: usize) -> Option<Bstr> {
    if i + 1 >= n {return None;}
    match &s[i..i + 2] {
        b"|-" => Some(Bstr::from("⊢")),
        b"->" => Some(Bstr::from("→")),
        b"/\\" => Some(Bstr::from("∧")),
        b"\\/" => Some(Bstr::from("∨")),
        b"<=" => Some(Bstr::from("≤")),
        _ => None
    }
}

fn in_sym3(s: &[u8], i: usize, n: usize) -> Option<Bstr> {
    if i + 2 >= n {return None;}
    match &s[i..i + 3] {
        b"<->" => Some(Bstr::from("↔")),
        _ => None
    }
}

const SYMBOL: u8 = 0;
const IDENT: u8 = 1;

static KEYWORDS: &[(&[u8], &str, u8)] = &[
    (b"Cap", "⋂", SYMBOL),
    (b"Complex", "ℂ", IDENT),
    (b"Cup", "⋃", SYMBOL),
    (b"Int", "ℤ", IDENT),
    (b"Nat", "ℕ", IDENT),
    (b"Rat", "ℚ", IDENT),
    (b"Real", "ℝ", IDENT),
    (b"and", "∧", SYMBOL),
    (b"begin", "begin", SYMBOL),
    (b"box", "□", SYMBOL),
    (b"cap", "∩", SYMBOL),
    (b"circ", "∘", SYMBOL),
    (b"cup", "∪", SYMBOL),
    (b"decl", "decl", SYMBOL),
    (b"dia", "◇", SYMBOL),
    (b"empty", "∅", SYMBOL),
    (b"end", "end", SYMBOL),
    (b"equiv", "≡", SYMBOL),
    (b"exists", "∃", SYMBOL),
    (b"false", "⊥", SYMBOL),
    (b"fn", "fn", SYMBOL),
    (b"forall", "∀", SYMBOL),
    (b"in", "∈", SYMBOL),
    (b"incl", "⊆", SYMBOL),
    (b"let", "let", SYMBOL),
    (b"not", "¬", SYMBOL),
    (b"or", "∨", SYMBOL),
    (b"times", "×", SYMBOL),
    (b"true", "⊤", SYMBOL)
];

static SYMBOL_MAP: &[(&str, &str)] = &[
    ("∅", "empty")
];

#[inline]
pub(crate) fn is_utf8_continuation_byte(byte: u8) -> bool {
    (byte & 0b1100_0000) == 0b1000_0000
}

/*
fn decode_utf8_unchecked(s: &[u8]) -> u32 {
    let s0 = s[0];
    if s0 < 0b11100000 {
        // 110xxxxx 10xxxxxx
        (((s0 & 0b11111) as u32) << 6) | ((s[1] & 0b111111) as u32)
    } else {
        // 1110xxxx 10xxxxxx 10xxxxxx
        (((s0 & 0b1111) as u32) << 12)
        | (((s[1] & 0b111111) as u32) << 6)
        |  ((s[2] & 0b111111) as u32)
    }
}

fn mb_is_alpha(s: &[u8]) -> bool {
    let x = decode_utf8_unchecked(s);
    !(x == 172 || x == 215 || (8590..10240).contains(&x))
}
*/

pub(crate) fn mb_is_alpha(s: &[u8]) -> bool {
    let Ok(st) = std::str::from_utf8(s) else { return false; };
    let Some(ch) = st.chars().next() else { return false; };
    let x = ch as u32;
    !(x == 172 || x == 215 || (8590..10240).contains(&x))
}

pub(crate) fn unicode_identifier(s: &[u8], mut i: usize, n: usize) -> usize {
    loop {
        if i >= n {return i;}
        if s[i] > 127 {
            let j = i; i += 1;
            while i < n && is_utf8_continuation_byte(s[i]) {i += 1;}
            if !mb_is_alpha(&s[j..i]) {return j;}
        } else if s[i].is_ascii_alphabetic() || s[i].is_ascii_digit() ||
            s[i] == b'_' || s[i] == b'\''
        {
            i += 1;
        } else {return i;}
    }
}

fn scan(s: &[u8]) -> Result<Vec<Token>, Error> {
    let mut i = 0;
    let n = s.len();
    let mut acc: Vec<Token> = Vec::new();
    let mut line: usize = 0;
    while i < n {
        if s[i].is_ascii_alphabetic() || s[i] == b'_' {
            let j = i;
            while i < n && (s[i].is_ascii_alphabetic() ||
                s[i].is_ascii_digit() ||
                matches!(s[i], b'_' | b'\''))
            {
                i += 1;
            }
            if i < n && s[i] > 127 {
                i = unicode_identifier(s, i, n);
            }
            let value = match KEYWORDS.binary_search_by_key(&&s[j..i], |t| t.0) {
                Ok(index) => {
                    let record = &KEYWORDS[index];
                    if record.2 == SYMBOL {
                        TokenValue::Symbol(Bstr::from(record.1))
                    } else {
                        TokenValue::Identifier(Bstr::from(record.1))
                    }
                },
                _ => TokenValue::Identifier(Bstr::from(&s[j..i]))
            };
            acc.push(Token {line, value});
        } else if s[i].is_ascii_digit() {
            while i < n && s[i] == b'0' {i += 1;}
            let j = i;
            while i < n && s[i].is_ascii_digit() {
                i += 1;
            }
            let value = TokenValue::Number(if i == j {
                Bstr::from("0")
            } else {
                Bstr::from(&s[j..i])
            });
            acc.push(Token {line, value});
        } else if s[i].is_ascii_whitespace() {
            if s[i] == b'\n' {line += 1;}
            i += 1;
        } else if let Some(x) = in_sym3(s, i, n) {
            let value = TokenValue::Symbol(x);
            acc.push(Token {line, value});
            i += 3;
        } else if let Some(x) = in_sym2(s, i, n) {
            let value = TokenValue::Symbol(x);
            acc.push(Token {line, value});
            i += 2;
        } else if s[i] == b'#' {
            while i < n && s[i] != b'\n' {i += 1;}
        } else if s[i] == b'(' && i + 1 < n && s[i + 1] == b'*' {
            let start_line = line;
            loop {
                if s[i] == b'*' && i + 1 < n && s[i + 1] == b')' {
                    i += 2;
                    break;
                }
                if s[i] == b'\n' {line += 1;}
                i += 1;
                if i == n {
                    return Err(syntax_error(start_line,
                        "unclosed comment".into()));
                }
            }
        } else if s[i] > 127 {
            let j = i; i += 1;
            while i < n && is_utf8_continuation_byte(s[i]) {i += 1;}
            let symbol = &s[j..i];
            let result = SYMBOL_MAP.iter().find(|&&(k, _)| symbol == k.as_bytes());
            let value = if let Some((_, value)) = result {
                TokenValue::Identifier(Bstr::from(*value))
            } else if mb_is_alpha(symbol) {
                i = unicode_identifier(s, i, n);
                TokenValue::Identifier(Bstr::from(&s[j..i]))
            } else {
                TokenValue::Symbol(Bstr::from(symbol))
            };
            acc.push(Token {line, value});
        } else {
            let value = TokenValue::Symbol(Bstr::from(&s[i..i+1]));
            acc.push(Token {line, value});
            i += 1;
        }
    }
    acc.push(Token {line, value: TokenValue::None});
    Ok(acc)
}

// Types. Type::Var occurs only during type inference (see Elab);
// there are no type variables in finalized terms or in `definitions`.
#[derive(Debug, Clone, PartialEq)]
enum Type {Prop, Ind, Fn(Rc<FnType>), Var(usize)}
use Type::{Prop, Ind};

// Function type A1 → ... → An → V (n >= 1), always applied with n
// arguments.
#[derive(Debug, PartialEq)]
struct FnType {
    argv: Vec<Type>,
    value: Type
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Prop => write!(f, "Prop"),
            Type::Ind => write!(f, "Ind"),
            Type::Var(n) => write!(f, "?{}", n),
            Type::Fn(t) => {
                for a in &t.argv {
                    match a {
                        Type::Fn(_) => write!(f, "({}) → ", a)?,
                        _ => write!(f, "{} → ", a)?
                    }
                }
                // A function value cannot be written directly, but can
                // arise during inference; parentheses make it visible.
                match &t.value {
                    Type::Fn(_) => write!(f, "({})", t.value),
                    v => write!(f, "{}", v)
                }
            }
        }
    }
}

// Abstraction: `term` in which occurrences of `args` are the formal
// parameters. This is the value of a higher-order predicate or
// function variable during matching (and in unification hints).
#[derive(Debug)]
struct Substitution {
    term: Term,
    args: Vec<Term>
}

impl Substitution {
    fn call(&self, argv: &[Term]) -> Term {
        replace_terms(&self.term, &self.args, argv)
    }
}

// Value of a pattern variable: an ordinary term or an abstraction.
#[derive(Debug, Clone)]
enum Binding {
    Term(Term),
    Abs(Rc<Substitution>)
}

// Bound variables are "locally nameless": inside an abstraction, a
// bound variable is a de Bruijn index (BoundVar(i) belongs to the
// i-th enclosing lambda, counted from the inside starting at 0).
// Alpha-equivalent terms are thereby identical; `term_eq` is structural
// equality. Descending under a binder (unify, free_in, eta_eq) opens it
// with a fresh free variable `Local`; the counter `Env::var_counter`
// exists solely for this purpose. Terms being processed are locally
// closed: no BoundVar points outside the term.
#[derive(Debug, Clone, PartialEq)]
enum TermValue {
    Var(Bstr),
    Const(Bstr),
    PatVar(Bstr),
    BoundVar(usize),
    Local(usize),
    App(Rc<[Term]>),
    Int(i64),
    // Body; the bound variable is BoundVar(0) within it. The type of
    // the term is Fn([variable type], body type).
    Lambda(Rc<Term>)
}

#[derive(Clone, PartialEq)]
struct Term {
    value: TermValue,
    ty: Type
}

impl Term {
    fn is_const(&self, ident: &str) -> bool {
        matches!(&self.value, Const(x) if x.as_slice() == ident.as_bytes())
    }

    fn arg(&self, k: usize) -> &Self {
        match &self.value {
            App(a) => &a[k],
            _ => unreachable!()
        }
    }

    pub fn as_connective(&self, ident: &str) -> Option<&[Term]> {
        match &self.value {
            App(a) if a.first().is_some_and(|h| h.is_const(ident)) => Some(&a[1..]),
            _ => None,
        }
    }

    pub fn as_unary(&self, ident: &str) -> Option<&Term> {
        match self.as_connective(ident) {
            Some([arg]) => Some(arg),
            _ => None,
        }
    }

    pub fn as_binary(&self, ident: &str) -> Option<(&Term, &Term)> {
        match self.as_connective(ident) {
            Some([lhs, rhs]) => Some((lhs, rhs)),
            _ => None,
        }
    }

    // Sequent H ⊢ A, read as □(H → A) with semantics "holds in all
    // interpretations and under all assignments". The sequent thus
    // closes all variables in its content: FV(H ⊢ A) = ∅. An occurrence
    // of a variable inside is not free and must not be affected by any
    // substitution (see `replace_terms`).
    // Not meant are modal operators `nec` and `pos` (□, ◇) of the
    // object language: they are ordinary connectives (e.g. Kripke
    // semantics with rigid variables); arguments keep free variables.
    fn is_closed_scope(&self) -> bool {
        matches!(self.as_binary("seq"), Some(_))
    }

    // `uq (fn x. A)` or `ex (fn x. A)`
    fn is_quantifier(&self) -> bool {
        if let Some(arg) = self.as_unary("uq") {
            matches!(arg.value, Lambda(_))
        } else if let Some(arg) = self.as_unary("ex") {
            matches!(arg.value, Lambda(_))
        } else {
            false
        }
    }
}

use TermValue::{Var, Const, PatVar, BoundVar, Local, App, Int, Lambda};

fn term(value: TermValue, ty: Type) -> Term {
    Term {value, ty}
}

fn app<const N: usize>(args: [Term; N], ty: Type) -> Term {
    term(App(Rc::new(args)), ty)
}

fn constant(ident: &str, ty: Type) -> Term {
    term(Const(Bstr::from(ident)), ty)
}

fn verum() -> Term {
    constant("verum", Prop)
}

fn conjunction(a: Term, b: Term) -> Term {
    app([constant("conj", prop_prop_prop()), a, b], Prop)
}

impl std::fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            if let App(_) = self.value {
                return write!(f, "{:#?}:{}", self.value, self.ty);
            }
        }
        write!(f, "{:?}:{}", self.value, self.ty)
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.value {
            Var(x) | Const(x) | PatVar(x) => write!(f, "{}", x),
            BoundVar(x) => write!(f, "${}", x),
            Local(x) => write!(f, "#{}", x),
            Int(x) => write!(f, "{}", x),
            App(a) => {
                write!(f, "(")?;
                let mut first = true;
                for x in a.as_ref() {
                    if first {first = false} else {write!(f, " ")?;}
                    write!(f, "{}", x)?;
                }
                write!(f, ")")
            },
            Lambda(t) => write!(f, "(lambda {})", t)
        }
    }
}

fn fn_type(argv: Vec<Type>, value: Type) -> Type {
    Type::Fn(Rc::new(FnType {argv, value}))
}

fn prop_prop_prop() -> Type {
    fn_type(vec![Prop, Prop], Prop)
}
// The types of operators, connectives, quantifiers etc. are not known
// to the checker. They are declared in the prelude (`RULES`) or in the
// theory with `decl name: Type.`, and live in `Env::definitions`,
// the only source of truth. What remains hardwired here is the types
// of the constants the kernel constructs itself (`seq`, `conj`,
// `subj`, `true`): see `verum`, `conjunction`, `theorem_sequent`,
// `auto_rule`, `verify_cb`.

// Surface syntax without types. Bound variables are already
// resolved: `Lam(b)` binds the variable `Bound(0)` in b; in general,
// `Bound(i)` is the variable of the i-th enclosing `Lam` (de Bruijn
// index, from inside starting at 0). Operators, quantifiers, and
// comprehensions are `App([Builtin(..), ..])`; the universal quantifier
// is `App([Builtin("uq"), Lam(..)])`.
#[derive(Debug, Clone)]
enum Expr {
    Ident(Bstr),
    Builtin(&'static str),
    Int(i64),
    Bound(usize),
    App(Vec<Expr>),
    Lam(Box<Expr>),
    // Type annotation (e : T)
    Ascribe(Box<Expr>, Type)
}

impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Ident(x) => write!(f, "{}", x),
            Expr::Builtin(x) => write!(f, "{}", x),
            Expr::Int(n) => write!(f, "{}", n),
            Expr::Bound(n) => write!(f, "${}", n),
            Expr::App(a) => {
                write!(f, "(")?;
                for (i, x) in a.iter().enumerate() {
                    if i > 0 {write!(f, " ")?;}
                    write!(f, "{}", x)?;
                }
                write!(f, ")")
            },
            Expr::Lam(b) => write!(f, "(fn {})", b),
            Expr::Ascribe(e, ty) => write!(f, "({} : {})", e, ty)
        }
    }
}


#[derive(PartialEq)]
enum Assoc {Left, Right}

// Precedence, associativity, and constant name (the type comes from
// `Env::definitions`)
fn init_infix_table() -> HashMap<&'static [u8], (u32, Assoc, &'static str)> {
    use Assoc::{Left as L, Right as R};
    HashMap::from([
        ("∘".as_bytes(), (90, L, "composition")),
        ("⋅".as_bytes(), (90, L, "mul")),
        ("*".as_bytes(), (90, L, "mul")),
        ("×".as_bytes(), (90, L, "product")),
        ("/".as_bytes(), (90, L, "div")),
        ("∩".as_bytes(), (90, L, "intersection")),
        ("\\".as_bytes(), (90, L, "diff")),
        ("+".as_bytes(), (80, L, "add")),
        ("-".as_bytes(), (80, L, "sub")),
        ("∪".as_bytes(), (80, L, "union")),
        ("<".as_bytes(), (70, L, "lt")),
        ("≤".as_bytes(), (70, L, "le")),
        ("⊆".as_bytes(), (70, L, "subset")),
        ("∈".as_bytes(), (70, L, "element")),
        ("=".as_bytes(), (70, L, "eq")),
        ("≡".as_bytes(), (70, L, "equivalent")),
        ("∧".as_bytes(), (50, L, "conj")),
        ("∨".as_bytes(), (40, L, "disj")),
        ("→".as_bytes(), (30, R, "subj")),
        ("↔".as_bytes(), (20, L, "equi")),
        ("⊢".as_bytes(), (10, R, "seq"))
    ])
}

// The prefix ⊢ (name "seq") stands for `seq true A`.
fn init_prefix_table() -> HashMap<&'static [u8], (u32, &'static str)> {
    HashMap::from([
        ("⋂".as_bytes(), (100, "Intersection")),
        ("⋃".as_bytes(), (100, "Union")),
        ("-".as_bytes(), (100, "minus")),
        ("/".as_bytes(), (100, "reciprocal")),
        ("~".as_bytes(), (60, "neg")),
        ("¬".as_bytes(), (60, "neg")),
        ("□".as_bytes(), (60, "nec")),
        ("◇".as_bytes(), (60, "pos")),
        ("⊢".as_bytes(), (10, "seq"))
    ])
}

#[derive(Debug, Clone)]
struct MacroDef {
    name: Bstr,
    params: Vec<Bstr>,
    body: Expr
}

pub struct Env {
    tokens: Vec<Token>,
    index: Cell<usize>,
    infix_table: HashMap<&'static [u8], (u32, Assoc, &'static str)>,
    prefix_table: HashMap<&'static [u8], (u32, &'static str)>,
    // Scope of bound variables during parsing (innermost binder
    // last); the position from the end is the de Bruijn index.
    scope: RefCell<Vec<Bstr>>,
    book: HashMap<Bstr, Term>,
    var_counter: Cell<usize>,
    definitions: HashMap<Bstr, Type>,
    macro_stack: Vec<Vec<MacroDef>>,
    pub auto_rule: bool,

    #[cfg(debug_assertions)]
    mismatch_trace: RefCell<Vec<(Term, Term)>>
}

fn fresh_id(env: &Env) -> usize {
    env.var_counter.set(env.var_counter.get() + 1);
    env.var_counter.get()
}

impl Env {
    pub fn new() -> Self {
        Self {
            tokens: Vec::new(),
            index: Cell::new(0),
            infix_table: init_infix_table(),
            prefix_table: init_prefix_table(),
            scope: RefCell::new(Vec::new()),
            book: HashMap::new(),
            var_counter: Cell::new(0),
            definitions: HashMap::new(),
            macro_stack: vec![Vec::new()],
            auto_rule: true,

            #[cfg(debug_assertions)]
            mismatch_trace: RefCell::new(Vec::new())
        }
    }
    fn lookup(&self) -> &Token {
        &self.tokens[self.index.get()]
    }
    fn advance(&self) {
        self.index.set(self.index.get() + 1);
    }
    // Fresh free variable with which a binder is opened.
    fn unique_variable(&self, ty: Type) -> Term {
        term(Local(fresh_id(self)), ty)
    }

    #[allow(dead_code)]
    fn reset(&mut self) {
        // Book and definitions are empty afterwards, also the prelude
        // (`load_prelude`) is gone.
        self.book.clear();
        self.definitions.clear();
        self.macro_stack = vec![Vec::new()];
        self.scope.borrow_mut().clear();
    }

    #[cfg(debug_assertions)]
    fn set_mismatch(&self, x: Term, y: Term) {
        self.mismatch_trace.borrow_mut().push((x, y));
    }
    #[cfg(debug_assertions)]
    fn print_mismatch(&self) {
        let a = self.mismatch_trace.borrow();
        println!("Traceback:\n");
        for (x, y) in a.iter() {
            println!("     {}: {}\nwith {}: {}\n", x, x.ty, y, y.ty);
        }
    }
}

// Replaces in `t` the variable with index `k` (relative to root of
// `t`) by `u`. Precondition: `u` has no loose indices (e.g. `Local`)
// and `t` only points out of itself with `k` (locally closed except
// for the opened binder). Neither shifting nor renaming is needed.
fn open_at(t: &Term, k: usize, u: &Term) -> Term {
    match &t.value {
        BoundVar(i) if *i == k => u.clone(),
        App(a) => term(App(Rc::from(a.iter().map(|s|
            open_at(s, k, u)).collect::<Vec<_>>())), t.ty.clone()),
        Lambda(b) => term(Lambda(Rc::new(open_at(b, k + 1, u))), t.ty.clone()),
        _ => t.clone()
    }
}

// Type of the bound variable of an abstraction.
fn binder_type(lam: &Term) -> Type {
    let Type::Fn(f) = &lam.ty else {unreachable!()};
    f.argv[0].clone()
}

// Body of an abstraction with the bound variable replaced by u.
fn open(lam: &Term, u: &Term) -> Term {
    let Lambda(body) = &lam.value else {unreachable!()};
    open_at(body, 0, u)
}

// Increases in `t` all indices pointing beyond `t` (index >= cutoff
// under `cutoff` lambdas) by d. Needed when a term with loose indices
// is placed under additional binders (see `replace_terms`).
fn shift_rec(t: &Term, d: usize, cutoff: usize) -> Term {
    match &t.value {
        BoundVar(i) if *i >= cutoff => term(BoundVar(*i + d), t.ty.clone()),
        App(a) => term(App(Rc::from(a.iter().map(|s|
            shift_rec(s, d, cutoff)).collect::<Vec<_>>())), t.ty.clone()),
        Lambda(b) => term(
            Lambda(Rc::new(shift_rec(b, d, cutoff + 1))), t.ty.clone()),
        _ => t.clone()
    }
}

fn shift(t: &Term, d: usize) -> Term {
    if d == 0 {t.clone()} else {shift_rec(t, d, 0)}
}

// Replaces in `t` each subterm equal to x[i] (up to renaming of
// bound variables, i.e. structurally) by u[i]. This yields the call
// of an abstraction: x are the formal parameters, u the arguments.
//
// The arguments u[i] may have loose indices (subs_rec calls `call`
// with arguments pointing to a binder at the call site). They are
// therefore shifted by the number of lambdas under which they are
// inserted; otherwise they would be captured by a binder of `t`. The
// formal parameters x[i] are locally closed.
//
// Inside sequents, NOTHING is replaced. There, all variables are
// bound (FV(H ⊢ A) = ∅, see `Term::is_closed_scope`), so they are not
// free occurrences of formal parameters, and replacement would not be
// beta reduction: (λt. ⊢ x = t) y is ⊢ x = t and not ⊢ x = y.
// Without this exception, with eq_subst and hint `P t ↔ ⊢ x = t` the
// false proposition x = y → (⊢ x = x) → (⊢ x = y) is provable.
// Do not remove!
fn replace_terms(t: &Term, x: &[Term], u: &[Term]) -> Term {
    replace_under(t, x, u, 0)
}

fn replace_under(t: &Term, x: &[Term], u: &[Term], depth: usize) -> Term {
    for i in 0..x.len() {
        if term_eq(t, &x[i]) {return shift(&u[i], depth);}
    }
    if t.is_closed_scope() {return t.clone();}
    match &t.value {
        App(a) => term(App(Rc::from(a.iter().map(|s|
            replace_under(s, x, u, depth)).collect::<Vec<_>>())), t.ty.clone()),
        Lambda(b) => term(
            Lambda(Rc::new(replace_under(b, x, u, depth + 1))), t.ty.clone()),
        _ => t.clone()
    }
}

// Type inference: Hindley-Milner without let-polymorphism. Every
// free name (variable or function symbol) has exactly one type
// within a formula. Bound variables have type Ind. Type variables
// that remain unbound at the end become Ind.
struct Elab<'a> {
    env: &'a Env,
    tvars: Vec<Option<Type>>,
    free: Vec<(Bstr, Type)>,
    // In the formula of a statement with the rule `decl` or `def`, an
    // operator constant which is not yet declared is treated like an
    // undeclared identifier: a free name whose type is inferred from
    // its use (for `def` from both sides of the equivalence or
    // equation). `definition` then declares it with that type. Other
    // undeclared constants in a definition remain free names, which the
    // check of the right hand side rejects.
    declaring: bool
}

impl<'a> Elab<'a> {
    fn new(env: &'a Env) -> Self {
        Elab {env, tvars: Vec::new(), free: Vec::new(), declaring: false}
    }

    fn fresh(&mut self) -> Type {
        self.tvars.push(None);
        Type::Var(self.tvars.len() - 1)
    }

    // Follows variable bindings at the root of the type.
    fn resolve(&self, t: &Type) -> Type {
        let mut t = t.clone();
        loop {
            let next = match &t {
                Type::Var(v) => self.tvars[*v].clone(),
                _ => None
            };
            match next {
                Some(u) => t = u,
                None => break
            }
        }
        t
    }

    fn occurs(&self, v: usize, t: &Type) -> bool {
        match self.resolve(t) {
            Type::Var(w) => v == w,
            Type::Fn(f) =>
                f.argv.iter().any(|x| self.occurs(v, x)) || self.occurs(v, &f.value),
            _ => false
        }
    }

    fn unify_ty(&mut self, a: &Type, b: &Type) -> bool {
        let a = self.resolve(a);
        let b = self.resolve(b);
        match (&a, &b) {
            (Type::Var(x), Type::Var(y)) if x == y => true,
            (Type::Var(x), _) => {
                if self.occurs(*x, &b) {return false;}
                self.tvars[*x] = Some(b.clone());
                true
            },
            (_, Type::Var(y)) => {
                if self.occurs(*y, &a) {return false;}
                self.tvars[*y] = Some(a.clone());
                true
            },
            (Prop, Prop) | (Ind, Ind) => true,
            (Type::Fn(f), Type::Fn(g)) => {
                f.argv.len() == g.argv.len() &&
                f.argv.iter().zip(g.argv.iter()).all(|(x, y)| self.unify_ty(x, y)) &&
                self.unify_ty(&f.value, &g.value)
            },
            _ => false
        }
    }

    // Fully resolved type; unbound variables remain visible.
    fn deep(&self, t: &Type) -> Type {
        match self.resolve(t) {
            Type::Fn(f) => fn_type(
                f.argv.iter().map(|x| self.deep(x)).collect(),
                self.deep(&f.value)),
            t => t
        }
    }

    fn zonk(&self, t: &Type) -> Type {
        default_ind(&self.deep(t))
    }

    fn zonk_term(&self, t: &Term) -> Term {
        let value = match &t.value {
            App(a) => App(Rc::from(a.iter().map(|x|
                self.zonk_term(x)).collect::<Vec<_>>())),
            Lambda(a) => Lambda(Rc::new(self.zonk_term(a))),
            v => v.clone()
        };
        term(value, self.zonk(&t.ty))
    }

    fn free_type(&mut self, x: &Bstr) -> Type {
        for (name, ty) in &self.free {
            if name == x {return ty.clone();}
        }
        let ty = self.fresh();
        self.free.push((x.clone(), ty.clone()));
        ty
    }

    fn elab(&mut self, e: &Expr) -> Result<Term, String> {
        match e {
            Expr::Ident(x) => match self.env.definitions.get(x) {
                Some(ty) => Ok(term(Const(x.clone()), ty.clone())),
                None => {
                    let ty = self.free_type(x);
                    Ok(term(Var(x.clone()), ty))
                }
            },
            // Operators, connectives, quantifiers: the constant must have
            // been declared (prelude or theory).
            Expr::Builtin(s) => {
                let name = Bstr::from(*s);
                match self.env.definitions.get(&name) {
                    Some(ty) => Ok(term(Const(name), ty.clone())),
                    None if self.declaring => {
                        let ty = self.free_type(&name);
                        Ok(term(Var(name), ty))
                    },
                    None => Err(format!(
                        "the constant '{}' used by this notation is not \
                         declared; declare it with `decl {} : <type>.`",
                        s, s))
                }
            },
            Expr::Int(n) => Ok(term(Int(*n), Ind)),
            // Binders initially always have type Ind. For higher
            // levels, the variable type would be specified or
            // inferred here.
            Expr::Bound(i) => Ok(term(BoundVar(*i), Ind)),
            Expr::Lam(body) => {
                let b = self.elab(body)?;
                let ty = fn_type(vec![Ind], b.ty.clone());
                Ok(term(Lambda(Rc::new(b)), ty))
            },
            Expr::Ascribe(e, ty) => {
                let t = self.elab(e)?;
                if !self.unify_ty(&t.ty, ty) {
                    return Err(format!(
                        "{} has type {}, but is annotated with type {}",
                        t, self.deep(&t.ty), ty));
                }
                Ok(t)
            },
            Expr::App(items) => {
                let mut v = Vec::with_capacity(items.len());
                v.push(self.elab(&items[0])?);
                for x in &items[1..] {
                    let a = self.elab(x)?;
                    v.push(a);
                }
                let ret = self.fresh();
                let want = fn_type(
                    v[1..].iter().map(|x| x.ty.clone()).collect(), ret.clone());
                let have = self.deep(&v[0].ty);
                let want_before = self.deep(&want);
                if !self.unify_ty(&v[0].ty, &want) {
                    return Err(match &have {
                        Type::Fn(ft) if ft.argv.len() != v.len() - 1 =>
                            format!("{} expects {} argument(s), but got {}",
                                v[0], ft.argv.len(), v.len() - 1),
                        Type::Fn(_) => format!(
                            "type error in application of {}: its type is {}, \
                             but the arguments require {}",
                            v[0], have, want_before),
                        _ => format!(
                            "{} has type {} and cannot be applied to arguments",
                            v[0], have)
                    });
                }
                Ok(term(App(Rc::from(v)), ret))
            }
        }
    }
}

fn default_ind(t: &Type) -> Type {
    match t {
        Type::Var(_) => Ind,
        Type::Fn(f) => fn_type(
            f.argv.iter().map(default_ind).collect(), default_ind(&f.value)),
        t => t.clone()
    }
}

// Phase 3: Type inference for a formula (type Prop).
#[allow(dead_code)]
fn elaborate(env: &Env, line: usize, e: &Expr) -> Result<Term, Error> {
    elaborate_in(env, line, e, false)
}

fn elaborate_in(env: &Env, line: usize, e: &Expr, declaring: bool)
-> Result<Term, Error>
{
    let mut el = Elab::new(env);
    el.declaring = declaring;
    let t = el.elab(e).map_err(|m| type_error(line, m))?;
    if !el.unify_ty(&t.ty, &Prop) {
        return Err(type_error(line, format!(
            "expected {} to be of type Prop, but its type is {}",
            t, el.deep(&t.ty))));
    }
    Ok(el.zonk_term(&t))
}


fn peek(env: &Env, k: usize) -> Option<&Token> {
    env.tokens.get(env.index.get() + k)
}

// Bound variables are already resolved during parsing.
fn resolve_name(env: &Env, id: &Bstr) -> Expr {
    for (i, name) in env.scope.borrow().iter().rev().enumerate() {
        if name == id {return Expr::Bound(i);}
    }
    Expr::Ident(id.clone())
}

fn binder(ident: &'static str, body: Expr) -> Expr {
    Expr::App(vec![Expr::Builtin(ident), Expr::Lam(Box::new(body))])
}

fn quantifier(env: &Env, ident: &'static str) -> Result<Expr, Error> {
    env.advance();
    let token = env.lookup();
    let TokenValue::Identifier(var) = &token.value else {
        return Err(syntax_error(token.line, "expected a variable".to_string()));
    };
    env.advance();
    let token = env.lookup();
    if !token.is_symbol(".") && !token.is_symbol(":") {
        return Err(syntax_error(token.line, "expected '.'".to_string()));
    }
    env.advance();
    env.scope.borrow_mut().push(var.clone());
    let body = formula(env, 0);
    env.scope.borrow_mut().pop();
    Ok(binder(ident, body?))
}

fn function_literal(env: &Env) -> Result<Expr, Error> {
    env.advance();
    let token = env.lookup();
    let TokenValue::Identifier(var) = &token.value else {
        return Err(syntax_error(token.line, "expected a variable".to_string()));
    };
    env.advance();
    let token = env.lookup();
    if !token.is_symbol(".") {
        return Err(syntax_error(token.line, "expected '.'".to_string()));
    }
    env.advance();
    env.scope.borrow_mut().push(var.clone());
    let body = formula(env, 0);
    env.scope.borrow_mut().pop();
    Ok(Expr::Lam(Box::new(body?)))
}

fn set_literal(env: &Env, x: Expr) -> Result<Expr, Error> {
    let singleton = |x: Expr| Expr::App(vec![Expr::Builtin("sg"), x]);
    let mut x = singleton(x);
    loop {
        if !env.lookup().is_symbol(",") {break;}
        env.advance();
        let y = formula(env, 0)?;
        x = Expr::App(vec![Expr::Builtin("union"), x, singleton(y)]);
    }
    let token = env.lookup();
    if !token.is_symbol("}") {
        return Err(syntax_error(token.line, "expected '}'".to_string()));
    }
    env.advance();
    Ok(x)
}

// {x | A} or a set enumeration {a, b, c}
fn comprehension(env: &Env) -> Result<Expr, Error> {
    env.advance();
    let token = env.lookup();
    let is_binder = matches!(&token.value, TokenValue::Identifier(_)) &&
        matches!(peek(env, 1), Some(t) if t.is_symbol("|"));
    if !is_binder {
        let x = formula(env, 0)?;
        return set_literal(env, x);
    }
    let TokenValue::Identifier(var) = &token.value else {unreachable!()};
    env.advance();
    env.advance();
    env.scope.borrow_mut().push(var.clone());
    let body = formula(env, 0);
    env.scope.borrow_mut().pop();
    let body = body?;
    let token = env.lookup();
    if !token.is_symbol("}") {
        return Err(syntax_error(token.line, "expected '}'".to_string()));
    }
    env.advance();
    Ok(binder("comp", body))
}


fn invalid_digit(line: usize, byte: u8) -> Error {
    syntax_error(line, format!("invalid digit: {}", byte))
}

fn parse_int(line: usize, x: &Bstr) -> Result<i64, Error> {
    let mut n: i64 = 0;
    for &byte in x.as_slice() {
        let digit = match byte.checked_sub(b'0') {
            None => return Err(invalid_digit(line, byte)),
            Some(digit) if digit > 9 => return Err(invalid_digit(line, byte)),
            Some(digit) => i64::from(digit)
        };
        n = n.checked_mul(10).and_then(|n| n.checked_add(digit))
            .ok_or_else(|| syntax_error(line,
                format!("number literal too large: {}", x)))?;
    }
    Ok(n)
}

// Names of types. Declared sorts would be added here later.
fn type_name(id: &Bstr) -> Option<Type> {
    match id.as_slice() {
        b"Prop" => Some(Prop),
        b"Ind" => Some(Ind),
        _ => None
    }
}

fn parse_type_atom(env: &Env) -> Result<Type, Error> {
    let token = env.lookup();
    let TokenValue::Identifier(id) = &token.value else {
        return Err(syntax_error(token.line, "expected a type".to_string()));
    };
    let Some(ty) = type_name(id) else {
        return Err(syntax_error(token.line, format!("unknown type '{}'", id)));
    };
    env.advance();
    Ok(ty)
}

// `arg → value`. A function type as return value is flattened:
// `A → (B → C)` is `(A, B) → C`, i.e. the binary function.
fn arrow(arg: Type, value: Type) -> Type {
    match value {
        Type::Fn(g) => {
            let mut argv = vec![arg];
            argv.extend(g.argv.iter().cloned());
            fn_type(argv, g.value.clone())
        },
        value => fn_type(vec![arg], value)
    }
}

// type ::= atom ['→' type];        (right-associative)
// atom ::= name | '(' type ')';
// `(A → B) → C` has a function as argument, `A → B → C` two arguments.
fn parse_type(env: &Env) -> Result<Type, Error> {
    let token = env.lookup();
    let arg = if token.is_symbol("(") {
        env.advance();
        let ty = parse_type(env)?;
        let token = env.lookup();
        if token.is_symbol(",") {
            return Err(syntax_error(token.line, "a function of several \
                arguments has the type A → B → C, not (A, B) → C".to_string()));
        }
        if !token.is_symbol(")") {
            return Err(syntax_error(token.line, "expected ')' in type".to_string()));
        }
        env.advance();
        ty
    } else {
        parse_type_atom(env)?
    };
    if env.lookup().is_symbol("→") {
        env.advance();
        Ok(arrow(arg, parse_type(env)?))
    } else {
        Ok(arg)
    }
}

// Head of an application: an identifier, possibly type-annotated.
fn is_head(e: &Expr) -> bool {
    match e {
        Expr::Ident(_) | Expr::Bound(_) => true,
        Expr::Ascribe(x, _) => is_head(x),
        _ => false
    }
}

fn nud(env: &Env) -> Result<Expr, Error> {
    let token = env.lookup();
    if let TokenValue::Identifier(id) = &token.value {
        env.advance();
        Ok(resolve_name(env, id))
    } else if token.is_symbol("⊥") {
        env.advance();
        Ok(Expr::Builtin("falsum"))
    } else if token.is_symbol("⊤") {
        env.advance();
        Ok(Expr::Builtin("verum"))
    } else if token.is_symbol("(") {
        env.advance();
        let mut x = formula(env, 0)?;
        if env.lookup().is_symbol(":") {
            env.advance();
            x = Expr::Ascribe(Box::new(x), parse_type(env)?);
        } else if env.lookup().is_symbol(",") {
            env.advance();
            let y = formula(env, 0)?;
            x = Expr::App(vec![Expr::Builtin("pair"), x, y]);
        }
        let token = env.lookup();
        if !token.is_symbol(")") {
            return Err(syntax_error(token.line, format!(
                "expected ')', but got '{:?}'", token.value)));
        }
        env.advance();
        Ok(x)
    } else if token.is_symbol("∀") {
        quantifier(env, "uq")
    } else if token.is_symbol("∃") {
        quantifier(env, "ex")
    } else if token.is_symbol("fn") {
        function_literal(env)
    } else if token.is_symbol("{") {
        comprehension(env)
    } else if let TokenValue::Number(x) = &token.value {
        env.advance();
        Ok(Expr::Int(parse_int(token.line, x)?))
    } else {
        if let TokenValue::Symbol(symbol) = &token.value {
            if let Some((bp, ident)) = env.prefix_table.get(symbol.as_slice()) {
                env.advance();
                let x = formula(env, *bp)?;
                return Ok(if *ident == "seq" {
                    Expr::App(vec![Expr::Builtin("seq"), Expr::Builtin("verum"), x])
                } else {
                    Expr::App(vec![Expr::Builtin(*ident), x])
                });
            }
        }
        Err(syntax_error(token.line, format!("unimplemented: {:?}", token.value)))
    }
}

fn is_arg_start(token: &Token) -> bool {
    matches!(&token.value, TokenValue::Identifier(_) | TokenValue::Number(_)) ||
    matches!(&token.value, TokenValue::Symbol(s)
        if matches!(s.as_slice(), b"(" | b"{"))
}

fn application(env: &Env) -> Result<Expr, Error> {
    let line0 = env.lookup().line;
    let x = nud(env)?;
    if !is_arg_start(env.lookup()) {
        return Ok(x);
    }
    let mut args: Vec<Expr> = vec![x];
    while is_arg_start(env.lookup()) {
        args.push(nud(env)?);
    }
    if !is_head(&args[0]) {
        return Err(syntax_error(line0,
            "predicate or function must be an identifier".to_string()));
    }
    Ok(Expr::App(args))
}

fn formula(env: &Env, rbp: u32) -> Result<Expr, Error> {
    let mut x = application(env)?;
    loop {
        let token = env.lookup();
        let TokenValue::Symbol(symbol) = &token.value else {break};
        let Some((lbp, assoc, ident)) = env.infix_table.get(symbol.as_slice()) else {break};
        if rbp >= *lbp {break;}
        let next_rbp = if *assoc == Assoc::Left {*lbp} else {*lbp - 1};
        env.advance();
        let y = formula(env, next_rbp)?;
        x = Expr::App(vec![Expr::Builtin(*ident), x, y]);
    }
    Ok(x)
}

// A formula with the line on which it begins (for error messages).
type Formula = (Expr, usize);

fn parse_formula(env: &Env) -> Result<Formula, Error> {
    env.scope.borrow_mut().clear();
    let line = env.lookup().line;
    Ok((formula(env, 0)?, line))
}

#[derive(Debug)]
struct RawSeq(Vec<Bstr>, Formula);

fn parse_ref_sequent(env: &Env) -> Result<RawSeq, Error> {
    let ctx = ref_context(env)?;
    let token = env.lookup();
    if token.is_symbol("⊢") {
        env.advance();
        Ok(RawSeq(ctx, parse_formula(env)?))
    } else {
        Err(syntax_error(token.line, "expected context".to_string()))
    }
}

#[derive(Debug)]
enum Sum<X, Y> {Left(X), Right(Y)}

#[derive(Debug)]
struct RawStatement {
    line: usize,
    label: Bstr,
    term: Sum<Formula, RawSeq>,
    rule: Vec<Bstr>,
    hint: Option<Formula>
}

fn parse_statement(env: &Env) -> Result<RawStatement, Error> {
    let token = env.lookup();
    let (label, line) = match &token.value {
        TokenValue::Identifier(x) | TokenValue::Number(x) =>
            (x.clone(), token.line),
        _ => return Err(syntax_error(token.line, "expected label".to_string()))
    };
    env.advance();
    let token = env.lookup();
    if !token.is_symbol(".") {
        return Err(syntax_error(token.line, "expected '.'".to_string()));
    }
    env.advance();
    let token = env.lookup();

    let term = if matches!(token.value, TokenValue::Number(_)) || token.is_symbol("⊢") {
        Sum::Right(parse_ref_sequent(env)?)
    } else {
        Sum::Left(parse_formula(env)?)
    };
    let token = env.lookup();
    if !token.is_symbol(",") {
        return Err(syntax_error(token.line, "expected ','".to_string()));
    }
    env.advance();
    let rule = rule_app(env)?;
    let token = env.lookup();
    let hint = if token.is_symbol(",") {
        env.advance();
        Some(parse_formula(env)?)
    } else {
        None
    };
    let token = env.lookup();
    if !token.is_symbol(".") {
        return Err(syntax_error(token.line, "expected '.'".to_string()));
    }
    env.advance();
    Ok(RawStatement {line, label, term, rule, hint})
}

#[derive(Debug)]
enum Item {
    Let(Expr, usize),
    Begin,
    End(usize),
    Decl(Bstr, Type, usize), // `decl name: Type.`
    Stmt(RawStatement)
}

// decl ::= 'decl' name ':' type '.'
// The name is the name of the constant, as it appears in `Expr::Builtin`
// (`conj`, `element`, ...), not the operator symbol.
fn parse_decl(env: &Env) -> Result<Item, Error> {
    let line = env.lookup().line;
    env.advance();
    let token = env.lookup();
    let TokenValue::Identifier(name) = &token.value else {
        return Err(syntax_error(token.line,
            "expected a name after 'decl'".to_string()));
    };
    let name = name.clone();
    env.advance();
    let token = env.lookup();
    if !token.is_symbol(":") {
        return Err(syntax_error(token.line,
            "expected ':' after the name in a declaration".to_string()));
    }
    env.advance();
    let ty = parse_type(env)?;
    let token = env.lookup();
    if !token.is_symbol(".") {
        return Err(syntax_error(token.line,
            "expected '.' after declaration".to_string()));
    }
    env.advance();
    Ok(Item::Decl(name, ty, line))
}

// Phase 1: syntax only. Nothing is expanded and nothing is checked.
fn parse_items(env: &Env) -> Result<Vec<Item>, Error> {
    let mut items = Vec::new();
    loop {
        let token = env.lookup();
        if matches!(token.value, TokenValue::None) {break;}
        if token.is_symbol("let") {
            env.advance();
            let (e, line) = parse_formula(env)?;
            let token = env.lookup();
            if !token.is_symbol(".") {
                return Err(syntax_error(token.line,
                    "expected '.' after macro definition".to_string()));
            }
            env.advance();
            items.push(Item::Let(e, line));
        } else if token.is_symbol("begin") {
            env.advance();
            items.push(Item::Begin);
        } else if token.is_symbol("end") {
            let line = token.line;
            env.advance();
            items.push(Item::End(line));
        } else if token.is_symbol("decl") {
            items.push(parse_decl(env)?);
        } else {
            items.push(Item::Stmt(parse_statement(env)?));
        }
    }
    Ok(items)
}


fn rule_app(env: &Env) -> Result<Vec<Bstr>, Error> {
    let mut acc: Vec<Bstr> = Vec::new();
    let token = env.lookup();
    let x = match &token.value {
        TokenValue::Identifier(x) | TokenValue::Number(x) => x,
        _ => return Err(syntax_error(token.line,
            "expected identifier or label".to_string()))
    };
    acc.push(x.clone());
    env.advance();
    loop {
        let token = env.lookup();
        match &token.value {
            TokenValue::Identifier(x) | TokenValue::Number(x) => {
                acc.push(x.clone());
                env.advance();
            },
            TokenValue::Symbol(s) if matches!(s.as_slice(), b"." | b",") =>
                break,
            _ => return Err(syntax_error(token.line,
                "expected identifier or label".to_string()))
        }
    }
    Ok(acc)
}

fn ref_context(env: &Env) -> Result<Vec<Bstr>, Error> {
    let mut acc: Vec<Bstr> = Vec::new();
    let token = env.lookup();
    if token.is_symbol("⊢") {
        return Ok(acc);
    }
    loop {
        let token = env.lookup();
        if let TokenValue::Number(x) = &token.value {
            acc.push(x.clone());
            env.advance();
        }
        let token = env.lookup();
        if !token.is_symbol(",") {break;}
        env.advance();
    }
    Ok(acc)
}

// Phase 2: Macros on Expr.
//
// Hygiene: Bound variables are already de Bruijn indices, free names
// are names (Expr::Ident); neither can capture the other. An argument
// points with its loose indices to binders at the call site and is
// shifted by their count when inserted under body binders
// (substitute_params). A macro body itself has no loose indices. Free
// names in the body remain free names: a binder at the call site does
// not capture them because binder resolution took place before
// expansion. Binder copies need no fresh numbers: alpha equality is
// equality.

fn lookup_macro<'a>(env: &'a Env, x: &Bstr) -> Option<&'a MacroDef> {
    for frame in env.macro_stack.iter().rev() {
        for m in frame.iter().rev() {
            if m.name == *x {return Some(m);}
        }
    }
    None
}

fn invalid_macro_def(line: usize) -> Error {
    syntax_error(line, "invalid macro definition".to_string())
}

// The name under which an expression in head position can denote a
// macro or a constant: an identifier, or the constant a notation
// stands for (`x ⊆ y` is `subset x y`). Constants and macros share one
// namespace.
fn head_name(e: &Expr) -> Option<Bstr> {
    match e {
        Expr::Ident(x) => Some(x.clone()),
        Expr::Builtin(s) => Some(Bstr::from(*s)),
        _ => None
    }
}

// The name introduced by a definition `lhs ↔ rhs` or `lhs = rhs`, read
// off the unexpanded formula (a macro of that name would be expanded
// away before `definition` sees it).
fn defined_name(e: &Expr) -> Option<Bstr> {
    let Expr::App(a) = e else {return None;};
    if a.len() != 3 ||
        !matches!(&a[0], Expr::Builtin(s) if *s == "eq" || *s == "equi")
    {
        return None;
    }
    let mut lhs = &a[1];
    loop {
        match lhs {
            Expr::Ascribe(x, _) => lhs = &**x,
            Expr::App(l) => lhs = l.first()?,
            _ => return head_name(lhs)
        }
    }
}

fn ensure_not_macro(env: &Env, line: usize, name: &Bstr) -> Result<(), Error> {
    if lookup_macro(env, name).is_some() {
        return Err(logic_error(line, format!(
            "{} is a macro and cannot be declared or defined", name)));
    }
    Ok(())
}

// `let x ↔ A.`, `let P x ↔ A`, `let f a b = t.` etc.
// (parameters are identifiers)
fn define_macro(env: &mut Env, line: usize, e: &Expr) -> Result<(), Error> {
    let Expr::App(a) = e else {return Err(invalid_macro_def(line));};
    let is_eq = matches!(&a[0], Expr::Builtin(s) if *s == "eq" || *s == "equi");
    if !is_eq || a.len() != 3 {return Err(invalid_macro_def(line));}
    let (name, params) = match &a[1] {
        Expr::Ident(x) => (x.clone(), Vec::new()),
        Expr::Builtin(s) => (Bstr::from(*s), Vec::new()),
        Expr::App(l) => {
            let Some(f) = head_name(&l[0]) else {
                return Err(invalid_macro_def(line));
            };
            let mut params: Vec<Bstr> = Vec::new();
            for p in &l[1..] {
                match p {
                    Expr::Ident(x) if !params.contains(x) => params.push(x.clone()),
                    _ => return Err(invalid_macro_def(line))
                }
            }
            (f, params)
        },
        _ => return Err(invalid_macro_def(line))
    };
    // A name is either a macro or a constant, not both.
    if env.definitions.contains_key(&name) {
        return Err(logic_error(line, format!(
            "{} is declared as a constant and cannot be a macro", name)));
    }
    // The parameters shadow macros of the same name in the body.
    let body = expand(env, line, &a[2], &params)?;
    let n = env.macro_stack.len();
    env.macro_stack[n - 1].push(MacroDef {name, params, body});
    Ok(())
}

// Increases in `e` all indices pointing beyond `e` by d.
fn shift_expr(e: &Expr, d: usize, cutoff: usize) -> Expr {
    match e {
        Expr::Bound(i) if *i >= cutoff => Expr::Bound(*i + d),
        Expr::App(a) => Expr::App(a.iter().map(|x|
            shift_expr(x, d, cutoff)).collect()),
        Expr::Lam(b) => Expr::Lam(Box::new(shift_expr(b, d, cutoff + 1))),
        Expr::Ascribe(x, ty) => Expr::Ascribe(
            Box::new(shift_expr(x, d, cutoff)), ty.clone()),
        _ => e.clone()
    }
}

// Substitutes arguments for parameters. `depth` is the number of
// body binders enclosing `e`; arguments' loose indices are shifted
// by that amount.
fn substitute_params(e: &Expr, params: &[Bstr], args: &[Expr], depth: usize)
-> Expr
{
    match e {
        Expr::Ident(x) => match params.iter().position(|p| p == x) {
            Some(i) if depth == 0 => args[i].clone(),
            Some(i) => shift_expr(&args[i], depth, 0),
            None => e.clone()
        },
        Expr::App(a) => Expr::App(a.iter().map(|x|
            substitute_params(x, params, args, depth)).collect()),
        Expr::Lam(b) => Expr::Lam(Box::new(
            substitute_params(b, params, args, depth + 1))),
        Expr::Ascribe(x, ty) => Expr::Ascribe(Box::new(
            substitute_params(x, params, args, depth)), ty.clone()),
        _ => e.clone()
    }
}

// Expands all macro calls in e. `shadow` are names currently acting
// as parameters and therefore are not macros.
fn expand(env: &Env, line: usize, e: &Expr, shadow: &[Bstr])
-> Result<Expr, Error>
{
    match e {
        Expr::Ident(x) if !shadow.contains(x) => match lookup_macro(env, x) {
            None => Ok(e.clone()),
            Some(m) if m.params.is_empty() => Ok(m.body.clone()),
            Some(m) => Err(syntax_error(line, format!(
                "the macro {} takes {} argument(s), which must be provided",
                x, m.params.len())))
        },
        // The constant of a notation: not subject to `shadow`, since
        // parameters are identifiers.
        Expr::Builtin(s) => {
            let x = Bstr::from(*s);
            match lookup_macro(env, &x) {
                None => Ok(e.clone()),
                Some(m) if m.params.is_empty() => Ok(m.body.clone()),
                Some(m) => Err(syntax_error(line, format!(
                    "the macro {} takes {} argument(s), which must be provided",
                    x, m.params.len())))
            }
        },
        Expr::Lam(b) =>
            Ok(Expr::Lam(Box::new(expand(env, line, b, shadow)?))),
        Expr::App(items) => {
            let args = items[1..].iter().map(|x| expand(env, line, x, shadow))
                .collect::<Result<Vec<_>, _>>()?;
            let head = match &items[0] {
                Expr::Ident(f) if !shadow.contains(f) => Some(f.clone()),
                Expr::Builtin(s) => Some(Bstr::from(*s)),
                _ => None
            };
            if let Some(f) = head && let Some(m) = lookup_macro(env, &f) {
                if m.params.len() != args.len() {
                    return Err(syntax_error(line, format!(
                        "the macro {} takes {} argument(s), but got {}",
                        f, m.params.len(), args.len())));
                }
                return Ok(substitute_params(&m.body, &m.params, &args, 0));
            }
            let mut v = Vec::with_capacity(items.len());
            v.push(items[0].clone());
            v.extend(args);
            Ok(Expr::App(v))
        },
        Expr::Ascribe(x, ty) => Ok(Expr::Ascribe(
            Box::new(expand(env, line, x, shadow)?), ty.clone())),
        _ => Ok(e.clone())
    }
}

// Phases 2 and 3 for a formula (only used by tests now).
#[cfg(test)]
fn formula_type_checked(env: &Env) -> Result<Term, Error> {
    let (e, line) = parse_formula(env)?;
    let e = expand(env, line, &e, &[])?;
    elaborate(env, line, &e)
}

#[derive(Debug)]
struct RefSeq(Vec<Bstr>, Term);

#[derive(Debug)]
struct Statement {
    line: usize,
    label: Bstr,
    term: Sum<Term, RefSeq>,
    rule: Vec<Bstr>,
    hint: Option<Term>
}

#[allow(dead_code)]
fn elaborate_formula(env: &Env, f: &Formula) -> Result<Term, Error> {
    elaborate_formula_in(env, f, false)
}

fn elaborate_formula_in(env: &Env, f: &Formula, declaring: bool)
-> Result<Term, Error>
{
    let (e, line) = f;
    let e = expand(env, *line, e, &[])?;
    elaborate_in(env, *line, &e, declaring)
}

fn elaborate_statement(env: &Env, raw: RawStatement) -> Result<Statement, Error> {
    let RawStatement {line, label, term, rule, hint} = raw;
    let declaring = rule[0].as_slice() == b"decl" || rule[0].as_slice() == b"def";
    if declaring {
        let (Sum::Left(f) | Sum::Right(RawSeq(_, f))) = &term;
        if let Some(name) = defined_name(&f.0) {
            ensure_not_macro(env, line, &name)?;
        }
    }
    let term = match term {
        Sum::Left(f) => Sum::Left(elaborate_formula_in(env, &f, declaring)?),
        Sum::Right(RawSeq(ctx, f)) =>
            Sum::Right(RefSeq(ctx, elaborate_formula_in(env, &f, declaring)?))
    };
    let hint = match hint {
        Some(f) => Some(elaborate_formula(env, &f)?),
        None => None
    };
    Ok(Statement {line, label, term, rule, hint})
}

fn dummy_sequent (a: Term) -> Term {
    app([constant("seq", prop_prop_prop()), verum(), a], Prop)
}

fn lookup<'a>(book: &'a HashMap<Bstr, Term>, key: &Bstr, line: usize)
-> Result<&'a Term, Error>
{
    match book.get(key) {
        Some(value) => Ok(value),
        None => Err(logic_error(line, format!("label '{}' not found", key)))
    }
}

fn pattern_from(t: &Term) -> Term {
    match &t.value {
        Var(x) => term(PatVar(x.clone()), t.ty.clone()),
        App(a) => term(App(Rc::from(a.iter().map(pattern_from)
            .collect::<Vec<_>>())), t.ty.clone()),
        Lambda(a) => term(Lambda(Rc::new(pattern_from(a))), t.ty.clone()),
        _ => t.clone()
    }
}

// Equality up to renaming of bound variables. With de Bruijn
// indices, this is structural equality (derive(PartialEq)): no fresh
// variables, no copies, no state.
fn term_eq(a: &Term, b: &Term) -> bool {
    a == b
}

mod substi {
    use {super::Binding, crate::Bstr};

    #[derive(Clone, Debug)]
    pub struct Subs(Vec<(Bstr, Binding)>);

    impl Subs {
        pub fn new() -> Self {
            Self(Vec::new())
        }
        pub fn set(&mut self, key: Bstr, value: Binding) {
            self.0.push((key, value));
        }
        pub fn get(&self, key: &Bstr) -> Option<&Binding> {
            for (k, v) in self.0.iter() {
                if *k == *key {return Some(v);}
            }
            None
        }
        pub fn set_to(&mut self, subs: Self) {
            self.0 = subs.0;
        }
    }
}
use substi::Subs;

fn has_patvar(t: &Term) -> bool {
    match &t.value {
        PatVar(_) => true,
        App(a) => a.iter().any(has_patvar),
        Lambda(a) => has_patvar(a),
        _ => false
    }
}

// Is x (a variable) free in t? Patterns are resolved with their
// bindings; an abstraction counts without its formal parameters.
// Sequents are intentionally searched anyway, even though their
// variables are semantically bound: this is conservative (it forbids
// at most too much) and keeps the eigenvariable condition safe.
fn free_in(env: &Env, x: &Term, t: &Term, subs: &Subs) -> bool {
    match &t.value {
        PatVar(id) => match subs.get(id) {
            Some(Binding::Term(v)) => free_in(env, x, v, subs),
            Some(Binding::Abs(s)) => {
                let holes: Vec<Term> = s.args.iter()
                    .map(|p| env.unique_variable(p.ty.clone())).collect();
                free_in(env, x, &s.call(&holes), subs)
            },
            None => t.ty == Ind && term_eq(x, t)
        },
        Var(_) | Const(_) => t.ty == Ind && term_eq(x, t),
        App(a) => a.iter().any(|y| free_in(env, x, y, subs)),
        Lambda(a) => free_in(env, x, a, subs),
        _ => false
    }
}

// Substitutes bindings into the pattern. If the head of an
// application is bound to an abstraction, beta-reduction is performed.
// Under a lambda of the pattern, arguments may have loose indices;
// `call` shifts them.
fn subs_rec(t: &Term, subs: &Subs) -> Term {
    match &t.value {
        PatVar(x) => match subs.get(x) {
            Some(Binding::Term(v)) => v.clone(),
            _ => t.clone()
        },
        App(a) => {
            let argv: Vec<Term> = a[1..].iter()
                .map(|x| subs_rec(x, subs)).collect();
            if let PatVar(f) = &a[0].value {
                match subs.get(f) {
                    Some(Binding::Abs(s)) if s.args.len() == argv.len() =>
                        return s.call(&argv),
                    Some(Binding::Term(g)) => {
                        let mut v = vec![g.clone()];
                        v.extend(argv);
                        return term(App(Rc::from(v)), t.ty.clone());
                    },
                    _ => {}
                }
            }
            let mut v = vec![subs_rec(&a[0], subs)];
            v.extend(argv);
            term(App(Rc::from(v)), t.ty.clone())
        },
        Lambda(a) => term(Lambda(Rc::new(subs_rec(a, subs))), t.ty.clone()),
        _ => t.clone()
    }
}

fn conj_list(t: &Term, subs: Option<&Subs>, acc: &mut Vec<Term>) {
    if t.is_const("verum") {
    } else if let Some((left, right)) = t.as_binary("conj") {
        conj_list(left, subs, acc);
        conj_list(right, subs, acc);
    } else if let Some(subs) = subs {
        conj_list(&subs_rec(t, subs), None, acc);
    } else {
        acc.push(t.clone());
    }
}

fn side_condition<'a>(form: &'a Term, conds: &mut Vec<(Term, Term)>) -> &'a Term {
    if let Some((hyp, rest)) = form.as_binary("subj") {
        if let Some((x, a)) = hyp.as_binary("nf") {
            conds.push((x.clone(), a.clone()));
            return side_condition(rest, conds);
        }
    }
    form
}

fn set_in(x: &Term, b: &[Term]) -> bool {
    b.iter().any(|y| term_eq(x, y))
}

fn subset(a: &[Term], b: &[Term]) -> bool {
    a.iter().all(|x| set_in(x, b))
}

fn set_eq(a: &[Term], b: &[Term]) -> bool {
    subset(a, b) && subset(b, a)
}

#[cfg(debug_assertions)]
macro_rules! trace {
    ($env:expr, $x:expr, $y:expr) => {$env.set_mismatch($x.clone(), $y.clone())}
}

#[cfg(not(debug_assertions))]
macro_rules! trace {
    ($env:expr, $x:expr, $y:expr) => {}
}

fn unify_seq(env: &Env, line: usize, a: &[Term], pattern: &[Term], subs: &mut Subs)
-> bool
{
    let result = unify(env, line, &a[2], &pattern[2], subs);
    if !result {trace!(env, a[2], pattern[2]); return false;}
    let mut l1 = Vec::new();
    let mut l2 = Vec::new();
    conj_list(&pattern[1], Some(subs), &mut l2);
    conj_list(&a[1], None, &mut l1);
    set_eq(&l1, &l2)
}

fn unify_args(env: &Env, line: usize, a: &[Term], b: &[Term], subs: &mut Subs)
-> bool
{
    if a.len() != b.len() {
        trace!(env,
            term(App(Rc::from(a)), Prop),
            term(App(Rc::from(b)), Prop));
        return false;
    }
    let mut subs_copy = subs.clone();
    for (x, pat) in a.iter().zip(b.iter()) {
        let result = unify(env, line, x, pat, subs);
        if !result {
            if a[0].is_const("seq") && b[0].is_const("seq") {
                let result = unify_seq(env, line, a, b, &mut subs_copy);
                if result {
                    subs.set_to(subs_copy);
                }
                return result;
            }
            trace!(env,
                term(App(Rc::from(a)), Prop),
                term(App(Rc::from(b)), Prop));
            return false;
        }
    }
    true
}

// Matching of t against pattern `F p1 ... pn`, whose head is a
// pattern variable.
//  - F bound to an abstraction: invoke and match.
//  - F bound to a term (function/predicate symbol): apply.
//  - F unbound, all arguments known (no free pattern variables):
//    abstraction over occurrences of arguments in t. This covers the
//    case of bound variables (Miller patterns) and rewriting
//    occurrences of known terms (eq_subst).
//  - F unbound, arguments still unknown: imitation. t = h t1 ... tn
//    yields F := h and matching of ti with pi.
//  - otherwise, only constant abstraction remains.
// Scope condition (Miller): Pattern variables stand outside all
// binders opened by `unify_quant` on descent. A binding must therefore
// contain no `Local` belonging to such a binder, else the variable
// outlives its scope (∀y. S y y would become ∃z. ∀y. S z y).
fn has_local(t: &Term) -> bool {
    match &t.value {
        Local(_) => true,
        App(a) => a.iter().any(has_local),
        Lambda(b) => has_local(b),
        _ => false
    }
}

// Like has_local, but for the body of an abstraction: subterms equal
// to a formal parameter are abstracted by `replace_terms` and do not
// count. Mirrors its behavior, even for closed scopes.
fn local_escapes(t: &Term, formals: &[Term]) -> bool {
    if formals.iter().any(|x| term_eq(t, x)) {return false;}
    if t.is_closed_scope() {return has_local(t);}
    match &t.value {
        Local(_) => true,
        App(a) => a.iter().any(|s| local_escapes(s, formals)),
        Lambda(b) => local_escapes(b, formals),
        _ => false
    }
}

fn unify_pred(env: &Env, line: usize, t: &Term, pattern: &[Term], subs: &mut Subs)
-> bool
{
    let PatVar(f) = &pattern[0].value else {unreachable!()};
    let args = &pattern[1..];
    match subs.get(f).cloned() {
        Some(Binding::Abs(s)) => {
            if s.args.len() != args.len() {return false;}
            let b = s.call(args);
            unify(env, line, t, &b, subs)
        },
        Some(Binding::Term(g)) => {
            let mut v = Vec::with_capacity(args.len() + 1);
            v.push(g);
            v.extend(args.iter().cloned());
            unify(env, line, t, &term(App(Rc::from(v)), t.ty.clone()), subs)
        },
        None => {
            let inst: Vec<Term> = args.iter()
                .map(|x| subs_rec(x, subs)).collect();
            if local_escapes(t, &inst) {
                trace!(env, t, pattern[0]);
                return false;
            }
            if !inst.iter().any(has_patvar) {
                let abs = Substitution {term: t.clone(), args: inst};
                subs.set(f.clone(), Binding::Abs(Rc::new(abs)));
                return true;
            }
            if let App(a) = &t.value && a.len() == pattern.len()
                && a[0].ty == pattern[0].ty
            {
                subs.set(f.clone(), Binding::Term(a[0].clone()));
                return a[1..].iter().zip(args.iter())
                    .all(|(x, p)| unify(env, line, x, p, subs));
            }
            let abs = Substitution {term: t.clone(), args: inst};
            subs.set(f.clone(), Binding::Abs(Rc::new(abs)));
            true
        }
    }
}

// Both abstractions are opened with the same fresh variable and the
// bodies are unified. (Not needed for comparisons without pattern
// variables: structural equality suffices there.)
fn unify_quant(env: &Env, line: usize, t: &Term, pattern: &Term, subs: &mut Subs)
-> bool
{
    let u = env.unique_variable(binder_type(t));
    unify(env, line, &open(t, &u), &open(pattern, &u), subs)
}

// Is t eta-equivalent to abstraction s, i.e. s(x1..xn) = t x1 .. xn?
fn eta_eq(env: &Env, t: &Term, s: &Substitution) -> bool {
    let Type::Fn(ft) = &t.ty else {return false;};
    if ft.argv.len() != s.args.len() {return false;}
    let holes: Vec<Term> = ft.argv.iter()
        .map(|ty| env.unique_variable(ty.clone())).collect();
    let lhs = s.call(&holes);
    let mut v = Vec::with_capacity(holes.len() + 1);
    v.push(t.clone());
    v.extend(holes.iter().cloned());
    term_eq(&lhs, &term(App(Rc::from(v)), ft.value.clone()))
}

fn unify(env: &Env, line: usize, t: &Term, pattern: &Term, subs: &mut Subs)
-> bool
{
    if pattern.ty != t.ty {
        trace!(env, t, pattern);
        return false;
    }
    match &pattern.value {
        PatVar(id) => match subs.get(id).cloned() {
            None => {
                if has_local(t) {
                    trace!(env, t, pattern);
                    return false;
                }
                subs.set(id.clone(), Binding::Term(t.clone()));
                true
            },
            Some(Binding::Term(b)) => {
                let result = term_eq(t, &b);
                if !result {trace!(env, t, b);}
                result
            },
            Some(Binding::Abs(s)) => eta_eq(env, t, &s)
        },
        App(b) => {
            if let PatVar(_) = &b[0].value {
                return unify_pred(env, line, t, b, subs);
            }
            match &t.value {
                App(a) => unify_args(env, line, a, b, subs),
                _ => {trace!(env, t, pattern); false}
            }
        },
        Lambda(_) => match &t.value {
            Lambda(_) => unify_quant(env, line, t, pattern, subs),
            _ => {trace!(env, t, pattern); false}
        },
        _ => {
            let result = term_eq(pattern, t);
            if !result {trace!(env, t, pattern);}
            result
        }
    }
}

fn unification_hint(line: usize, hint: &Term, subs: &mut Subs)
-> Result<(), Error>
{
    if let Some((lhs, rhs)) = hint.as_binary("equi")
        .or_else(|| hint.as_binary("eq"))
    {
        if let App(a) = &lhs.value {
            let f = &a[0]; let args = &a[1..];
            if let Var(id) = &f.value {
                let abs = Substitution {term: rhs.clone(), args: args.to_vec()};
                subs.set(id.clone(), Binding::Abs(Rc::new(abs)));
            }
            return Ok(());
        }
    }
    Err(logic_error(line, format!("invalid unification hint: {}", hint)))
}

fn is_quantifier_rule(c: &Term) -> Option<&Term> {
    if let Some((_, seq)) = c.as_binary("subj") {
        if let Some((_, form)) = seq.as_binary("seq") {
            if form.is_quantifier() {
                return Some(seq);
            }
        }
    }
    None
}


fn gen_schema_variable(i: usize) -> Term {
    term(Var(Bstr::from(format!("H{}*", i).as_str())), Prop)
}

fn nested_conj(i: usize, n: usize) -> Term {
    let head = gen_schema_variable(i);
    if i == n {
        head
    } else {
        app([constant("conj", prop_prop_prop()), head, nested_conj(i + 1, n)], Prop)
    }
}

// Automatically applies
// lift_impl. (⊢ A → B) → (H ⊢ A) → (H ⊢ B), axiom.
// lift_impl_ii. (⊢ A → B → C) → (H1 ⊢ A) → (H2 ⊢ B) → (H1 ∧ H2 ⊢ C), axiom.
// and so on.
fn auto_rule(line: usize, a: &Term, i: usize, n: usize) -> Result<Term, Error> {
    if i == n + 1 {
        Ok(app([constant("seq", prop_prop_prop()), nested_conj(1, n), a.clone()], Prop))
    } else if let Some((a1, a2)) = a.as_binary("subj") {
        let head = app([constant("seq", prop_prop_prop()), gen_schema_variable(i), a1.clone()], Prop);
        let tail = auto_rule(line, a2, i + 1, n)?;
        Ok(app([constant("subj", prop_prop_prop()), head, tail], Prop))
    } else {
        Err(logic_error(line, format!(
            "expected a subjunction for premise {}", i)))
    }
}

fn conclusion(env: &Env, line: usize, b: &Term, c: &Term, subs: &mut Subs, args: &[Bstr])
-> Result<(), Error>
{
    #[cfg(debug_assertions)]
    env.mismatch_trace.borrow_mut().clear();

    let result = unify(env, line, b, c, subs);
    if !result {
        #[cfg(debug_assertions)] {
            env.print_mismatch();
        }
        return Err(logic_error(line,
            format!("unification failed for {}, in conclusion", args[0])));
    }
    Ok(())
}

fn modus_ponens(env: &Env, line: usize, b: &Term, args: &[Bstr], hint: Option<Term>)
-> Result<(), Error>
{
    let c = lookup(&env.book, &args[0], line)?;
    let c0 = if env.auto_rule && args.len() > 1 &&
        let Some((top, form)) = c.as_binary("seq")
    {
        if !top.is_const("verum") {
            return Err(logic_error(line,
                format!("'{}' does not correspond to a rule", args[0])));
        }
        pattern_from(&auto_rule(line, form, 1, args.len() - 1)?)
    } else {
        pattern_from(c)
    };
    let mut conds: Vec<(Term, Term)> = Vec::new();
    let mut c = side_condition(&c0, &mut conds);

    let mut subs = Subs::new();
    let mut reverse = false;
    if let Some(hint) = hint {
        unification_hint(line, &hint, &mut subs)?;
    }
    if let Some(c2) = is_quantifier_rule(c) {
        conclusion(env, line, b, c2, &mut subs, args)?;
        reverse = true;
    }
    for i in 1..args.len() {
        let a = lookup(&env.book, &args[i], line)?;
        let Some((c1, c2)) = c.as_binary("subj") else {
            return Err(logic_error(line, "expected a rule/subjunction".to_string()));
        };

        #[cfg(debug_assertions)]
        env.mismatch_trace.borrow_mut().clear();

        let result = unify(env, line, a, c1, &mut subs);
        if !result {
            #[cfg(debug_assertions)] {
                env.print_mismatch();
            }
            return Err(logic_error(line,
                format!("unification failed for {}, argument {}", args[0], i)));
        }
        c = c2;
    }
    if !reverse {
        conclusion(env, line, b, c, &mut subs, args)?;
    }
    for (x, a) in &conds {
        let mut x = x;
        let mut unbound = false;
        if let PatVar(id) = &x.value {
            match subs.get(id) {
                Some(Binding::Term(x_subs)) => {x = x_subs;},
                None => {unbound = true;},
                _ => {}
            }
        }
        if !unbound && !matches!(x.value, Var(_)) {
            return Err(logic_error(line, format!(
                "in {}: {} is not a variable", args[0], x)));
        }
        if free_in(env, x, a, &subs) {
            let inst = subs_rec(a, &subs);
            return Err(logic_error(line, format!(
                "in {}: {} occurs free in {}", args[0], x, inst)));
        }
    }
    Ok(())
}

fn free_vars(env: &Env, a: &Term, s: &mut HashMap<Bstr, ()>) {
    match &a.value {
        Var(id) | Const(id) => {
            if !env.definitions.contains_key(id) {
                s.insert(id.clone(), ());
            }
        },
        App(a) => {
            for b in a.iter() {
                free_vars(env, b, s);
            }
        },
        Lambda(a) => {
            free_vars(env, a, s);
        },
        _ => {}
    }
}

fn expect_len(line: usize, args: &[Bstr], n: usize, rule_name: &str)
-> Result<(), Error>
{
    let s = if n == 1 {""} else {"s"};
    Err(logic_error(line, format!(
        "rule {} expects {} argument{}, but got {}",
        rule_name, n, s, args.len())))
}

fn free_vars_check(env: &Env, line: usize, a: &Term, argv: &[Term]) -> Result<(), Error> {
    let mut s = HashMap::new();
    free_vars(env, a, &mut s);
    for x in s.keys() {
        if !argv.iter().any(|arg|
            matches!(&arg.value, Const(id) | Var(id) if id == x))
        {
            println!("{:?}", a);
            return Err(logic_error(line, format!(
                "{} is free in right hand side of definition", x)));
        }
    }
    Ok(())
}

// Does any parameter occur in a sequent in t? There it is bound
// (FV(H ⊢ A) = ∅); □ and ◇ of the object language do not count.
// Otherwise, the definition equation would become false upon
// substituting for the parameter: `p x y ↔ (⊢ x = y)` would yield
// `p a a ↔ (⊢ a = a)`, even though the RHS is independent of x and y.
fn param_in_closed_scope(t: &Term, params: &[Term], inside: bool) -> bool {
    match &t.value {
        Var(x) | Const(x) => inside && params.iter().any(
            |p| matches!(&p.value, Var(y) | Const(y) if y == x)),
        App(a) => {
            let inside = inside || t.is_closed_scope();
            a.iter().any(|s| param_in_closed_scope(s, params, inside))
        },
        Lambda(a) => param_in_closed_scope(a, params, inside),
        _ => false
    }
}

fn theorem_sequent(t: Term) -> Term {
    app([constant("seq", prop_prop_prop()), verum(), t], Prop)
}

fn definition(env: &mut Env, line: usize, seq: &mut Term, args: &[Bstr])
-> Result<(), Error>
{
    if args.len() != 1 {
        return expect_len(line, args, 0, "def");
    }
    let Some((top, c)) = seq.as_binary("seq") else {
        return Err(logic_error(line, "definition expects a sequent".to_string()));
    };
    if !top.is_const("verum") {
        return Err(logic_error(line, "definition expects empty context".to_string()));
    }
    let (con, a, b) = if let Some((a, b)) = c.as_binary("equi") {
        (c.arg(0), a, b)
    } else if let Some((a, b)) = c.as_binary("eq") {
        (c.arg(0), a, b)
    } else {
        return Err(logic_error(line, "malformed definition".to_string()));
    };
    match &a.value {
        Var(id) | Const(id) =>  {
            if env.definitions.contains_key(id) {
                return Err(logic_error(line, "already defined".to_string()));
            }
            free_vars_check(env, line, b, &[])?;
            env.definitions.insert(id.clone(), a.ty.clone());
            *seq = theorem_sequent(app([
                con.clone(),
                term(Const(id.clone()), a.ty.clone()),
                b.clone()
            ], c.ty.clone()));
        },
        App(args) => {
            let (Var(id) | Const(id)) = &args[0].value else {
                return Err(logic_error(line, "expected identifier".to_string()));
            };
            if env.definitions.contains_key(id) {
                return Err(logic_error(line, "already defined".to_string()));
            }
            free_vars_check(env, line, b, &args[1..])?;
            if param_in_closed_scope(b, &args[1..], false) {
                return Err(logic_error(line, format!(
                    "parameter of {} occurs inside a sequent on the \
                    right hand side, where it is bound", id)));
            }
            env.definitions.insert(id.clone(), args[0].ty.clone());
            let mut args = args.to_vec();
            args[0] = term(Const(id.clone()), args[0].ty.clone());
            *seq = theorem_sequent(app([
                con.clone(),
                term(App(Rc::from(args)), a.ty.clone()),
                b.clone()
            ], c.ty.clone()));
        },
        _ => {
            return Err(logic_error(line, "malformed definition".to_string()));
        }
    }
    Ok(())
}

// `decl name : Type.` introduces a symbol and its type. No logical
// content, no book entry.
fn declare(env: &mut Env, line: usize, name: Bstr, ty: Type)
-> Result<(), Error>
{
    if env.definitions.contains_key(&name) {
        return Err(logic_error(line, format!("{} is already defined", name)));
    }
    ensure_not_macro(env, line, &name)?;
    env.definitions.insert(name, ty);
    Ok(())
}

fn calc_unary(line: usize, x: &Term, op: fn(x: i64) -> Option<i64>)
-> Result<Option<Term>, Error>
{
    let x = calc_term(line, x)?;
    if let Int(x) = x.value {
        let Some(value) = op(x) else {
            return Err(logic_error(line, "arithmetic overflow".into()));
        };
        return Ok(Some(term(Int(value), Ind)));
    }
    Ok(None)
}

fn calc_binary(line: usize, x: &Term, y: &Term, op: fn(x: i64, y: i64) -> Option<i64>)
-> Result<Option<Term>, Error>
{
    let x = calc_term(line, x)?;
    let y = calc_term(line, y)?;
    if let Int(x) = x.value {
        if let Int(y) = y.value {
            let Some(value) = op(x, y) else {
                return Err(logic_error(line, "arithmetic overflow".into()));
            };
            return Ok(Some(term(Int(value), Ind)));
        }
    }
    Ok(None)
}

fn calc_term(line: usize, t: &Term) -> Result<Term, Error> {
    if let App(a) = &t.value {
        if let Const(f) = &a[0].value {
            if let Some(value) = match f.as_slice() {
                b"minus" => calc_unary(line, &a[1], i64::checked_neg)?,
                b"add" => calc_binary(line, &a[1], &a[2], i64::checked_add)?,
                b"sub" => calc_binary(line, &a[1], &a[2], i64::checked_sub)?,
                b"mul" => calc_binary(line, &a[1], &a[2], i64::checked_mul)?,
                _ => None
            } {
                return Ok(value);
            }
        }
    }
    Ok(t.clone())
}

fn calc_assert(line: usize, a: &Term, b: &Term, f: fn(i64, i64) -> bool)
-> Result<(), Error>
{
    let a = calc_term(line, a)?;
    let b = calc_term(line, b)?;
    if let Int(a) = a.value && let Int(b) = b.value {
        if f(a, b) {Ok(())} else {
            Err(logic_error(line, "calculation failed".to_string()))
        }
    } else {
        Err(logic_error(line, "calc expects number expressions".to_string()))
    }
}

fn calculate(line: usize, seq: &Term, args: &[Bstr])
-> Result<(), Error>
{
    if args.len() != 1 {
        return expect_len(line, args, 0, "calc");
    }
    let Some((top, c)) = seq.as_binary("seq") else {
        return Err(logic_error(line, "calc expects a sequent".to_string()));
    };
    if !top.is_const("verum") {
        return Err(logic_error(line, "calc expects empty context".to_string()));
    }
    if let Some(c1) = c.as_unary("neg") {
        if let Some((a, b)) = c1.as_binary("eq") {
            calc_assert(line, a, b, |x, y| x != y)
        } else if let Some((a, b)) = c1.as_binary("le") {
            calc_assert(line, a, b, |x, y| !(x <= y))
        } else if let Some((a, b)) = c1.as_binary("lt") {
            calc_assert(line, a, b, |x, y| !(x < y))
        } else {
            Err(logic_error(line, "unexpected term in calculation".to_string()))
        }
    } else if let Some((a, b)) = c.as_binary("eq") {
        calc_assert(line, a, b, |x, y| x == y)
    } else if let Some((a, b)) = c.as_binary("le") {
        calc_assert(line, a, b, |x, y| x <= y)
    } else if let Some((a, b)) = c.as_binary("lt") {
        calc_assert(line, a, b, |x, y| x < y)
    } else if let Some((tx, s)) = c.as_binary("element") {
        let x = calc_term(line, tx)?;
        let Int(x_value) = x.value else {
            return Err(logic_error(line, "calc expected number literal".to_string()));
        };
        if !(s.is_const("ℕ") || s.is_const("ℤ") || s.is_const("ℚ") ||
             s.is_const("ℝ") || s.is_const("ℂ"))
        {
            return Err(logic_error(line, "calc expected number set".to_string()));
        }
        if s.is_const("ℕ") && x_value < 0 {
            return Err(logic_error(line,
                "expected natural number, but got negative number".to_string()));
        }
        Ok(())
    } else {
        Err(logic_error(line, "unexpected term in calculation".to_string()))
    }
}

fn verify_cb(env: &mut Env, stmt: Statement) -> Result<(), Error> {
    let Statement {line, label, term, rule, hint} = stmt;
    let rule_key = rule[0].as_slice();
    let mut form = match term {
        Sum::Right(seq) => {
            let ctx = seq.0;
            let a = seq.1;
            env.book.insert(label.clone(), dummy_sequent(a.clone()));
            let mut h = verum();
            for k in ctx {
                let seq_k = lookup(&env.book, &k, line)?;
                let Some((_, form_k)) = seq_k.as_binary("seq") else {
                    return Err(logic_error(line,
                        format!("'{}' is not a sequent", k)));
                };
                h = conjunction(h, form_k.clone());
            }
            app([constant("seq", prop_prop_prop()), h, a], Prop)
        },
        Sum::Left(form) => form
    };
    if rule.iter().any(|x| *x == label) {
        return Err(logic_error(line, "cyclic deduction".to_string()));
    }
    if rule_key == b"def" {
        definition(env, line, &mut form, &rule)?;
    } else if rule_key == b"calc" {
        calculate(line, &form, &rule)?;
    } else if rule_key != b"axiom" && rule_key != b"rule" {
        modus_ponens(env, line, &form, &rule, hint)?;
    }
    env.book.insert(label.clone(), form);
    Ok(())
}

pub fn verify(env: &mut Env, s: &[u8]) -> Result<(), Error> {
    env.tokens = scan(s)?;
    env.index.set(0);
    let items = parse_items(env)?;
    for item in items {
        match item {
            Item::Let(e, line) => define_macro(env, line, &e)?,
            Item::Begin => env.macro_stack.push(Vec::new()),
            Item::End(line) => {
                if env.macro_stack.len() <= 1 {
                    return Err(syntax_error(line,
                        "'end' without matching 'begin'".to_string()));
                }
                env.macro_stack.pop();
            },
            Item::Decl(name, ty, line) => declare(env, line, name, ty)?,
            Item::Stmt(raw) => {
                let stmt = elaborate_statement(env, raw)?;
                verify_cb(env, stmt)?;
            }
        }
    }
    Ok(())
}

pub static PRELUDE: &str = "
decl falsum: Prop.
decl verum: Prop.
decl conj: Prop → Prop → Prop.
decl disj: Prop → Prop → Prop.
decl subj: Prop → Prop → Prop.
decl equi: Prop → Prop → Prop.
decl seq: Prop → Prop → Prop.
decl neg: Prop → Prop.
decl uq: (Ind → Prop) → Prop.
decl ex: (Ind → Prop) → Prop.
decl eq: Ind → Ind → Prop.
decl nf: Ind → Prop → Prop.

hypo. (⊤ ∧ A ⊢ A), axiom.
conj_intro. (H1 ⊢ A) → (H2 ⊢ B) → (H1 ∧ H2 ⊢ A ∧ B), axiom.
conj_eliml. (H ⊢ A ∧ B) → (H ⊢ A), axiom.
conj_elimr. (H ⊢ A ∧ B) → (H ⊢ B), axiom.
disj_introl. (H ⊢ A) → (H ⊢ A ∨ B), axiom.
disj_intror. (H ⊢ B) → (H ⊢ A ∨ B), axiom.
disj_elim. (H1 ⊢ A ∨ B) → (H2 ∧ A ⊢ C) → (H3 ∧ B ⊢ C) →
  (H1 ∧ H2 ∧ H3 ⊢ C), axiom.
subj_intro. (H ∧ A ⊢ B) → (H ⊢ A → B), axiom.
subj_elim. (H1 ⊢ A → B) → (H2 ⊢ A) → (H1 ∧ H2 ⊢ B), axiom.
neg_intro. (H ∧ A ⊢ ⊥) → (H ⊢ ¬A), axiom.
neg_elim. (H1 ⊢ ¬A) → (H2 ⊢ A) → (H1 ∧ H2 ⊢ ⊥), axiom.
equi_intro. (H1 ⊢ A → B) → (H2 ⊢ B → A) → (H1 ∧ H2 ⊢ A ↔ B), axiom.
equi_eliml. (H ⊢ A ↔ B) → (H ⊢ A → B), axiom.
equi_elimr. (H ⊢ A ↔ B) → (H ⊢ B → A), axiom.
wk. (H ⊢ B) → (H ∧ A ⊢ B), axiom.
exch. (H ⊢ A) → (H ⊢ A), axiom.
uq_intro. (nf u (H ∧ ∀x. A x)) → (H ⊢ A u) → (H ⊢ ∀x. A x), axiom.
uq_elim. (H ⊢ ∀x. A x) → (H ⊢ A t), axiom.
ex_intro. (H ⊢ A t) → (H ⊢ ∃x. A x), axiom.
ex_elim. (nf u (H1 ∧ H2 ∧ B ∧ ∃x. A x)) →
  (H1 ⊢ ∃x. A x) → (H2 ∧ A u ⊢ B) → (H1 ∧ H2 ⊢ B), axiom.
subj_intro_ii. (H ∧ A ∧ B ⊢ C) → (H ⊢ A → B → C), axiom.
subj_intro_iii. (H ∧ A ∧ B ∧ C ⊢ D) → (H ⊢ A → B → C → D), axiom.
subj_intro_iv. (H ∧ A ∧ B ∧ C ∧ D ⊢ E) → (H ⊢ A → B → C → D → E), axiom.
";

#[allow(dead_code)]
pub fn load_prelude(env: &mut Env) {
    if verify(env, PRELUDE.as_bytes()).is_err() {
        unreachable!();
    }
}

