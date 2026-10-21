//! The Djinn AST: declarations, statements (constraints) and expressions.
//! Every statement and expression carries the span of its source tokens, so
//! that errors found while lowering point at the construct, not at the
//! declaration.

use proc_macro2::{Span, TokenStream};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Func,
    Rel,
}

impl Kind {
    pub fn word(self) -> &'static str {
        match self {
            Kind::Func => "func",
            Kind::Rel => "rel",
        }
    }
    pub fn from_word(s: &str) -> Kind {
        match s {
            "rel" => Kind::Rel,
            _ => Kind::Func,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SeqKind {
    Slice,
    Vec,
    /// `[T; N]`, with the length tokens as written.
    Array(String),
    /// `&str`: a byte string (Aeneas models `str` as `Slice U8`).
    Str,
    /// `String`: an owned string, viewed as its UTF-8 bytes (Aeneas keeps
    /// Lean's `String` as the carrier; the trusted models bridge it).
    String,
}

/// Rust types the specification language understands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RType {
    /// Machine integer; `bits == 0` means pointer-sized (`usize`/`isize`).
    Int { signed: bool, bits: u32 },
    /// The mathematical integer `int`: allowed only in `rel` signatures,
    /// which are never implemented.
    MathInt,
    Bool,
    Char,
    Seq(Box<RType>, SeqKind),
    /// `HashMap<K, V>`: viewed as the list of its entries, no key twice
    /// (modeled by the trusted library, DESIGN.md §6).
    Map(Box<RType>, Box<RType>),
    Option(Box<RType>),
    Result(Box<RType>, Box<RType>),
    Unit,
    /// A user type (`struct`/`enum` declared next to the block), by name.
    Named(String),
}

impl RType {
    pub fn is_scalar(&self) -> bool {
        matches!(self, RType::Int { .. })
    }
    pub fn is_numeric(&self) -> bool {
        matches!(self, RType::Int { .. } | RType::MathInt)
    }
    pub fn is_signed_scalar(&self) -> bool {
        matches!(self, RType::Int { signed: true, .. })
    }
    pub fn is_seq(&self) -> bool {
        matches!(self, RType::Seq(..))
    }
    pub fn elem(&self) -> Option<&RType> {
        match self {
            RType::Seq(e, _) => Some(e),
            _ => None,
        }
    }
    /// Does the type mention a user type?
    pub fn mentions_named(&self) -> bool {
        match self {
            RType::Named(_) => true,
            RType::Seq(e, _) | RType::Option(e) => e.mentions_named(),
            RType::Result(a, b) | RType::Map(a, b) => a.mentions_named() || b.mentions_named(),
            _ => false,
        }
    }
    /// Does the type need the Aeneas `Types` module (a user type, or a
    /// modeled standard type defined in `TypesExternal`)?
    pub fn needs_code_types(&self) -> bool {
        match self {
            RType::Named(_) | RType::Map(..) => true,
            RType::Seq(e, _) | RType::Option(e) => e.needs_code_types(),
            RType::Result(a, b) => a.needs_code_types() || b.needs_code_types(),
            _ => false,
        }
    }
}

/// The type of a specification-level term. `Int` is the unbounded
/// mathematical integer of constraints; everything else is a Rust type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SType {
    Int,
    Of(RType),
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub ty: RType,
    /// `&mut T`: the parameter is also an output.
    pub mut_ref: bool,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Decl {
    pub kind: Kind,
    pub name: String,
    pub name_span: Span,
    pub params: Vec<Param>,
    /// Named return value, if the return type is not `()`.
    pub ret: Option<(String, RType)>,
    pub requires: Vec<Expr>,
    pub ensures: Vec<Expr>,
    pub total: bool,
    /// `#[override_smoke_test]`: the smoke-test skips this declaration (its
    /// bounded search is known to be inconclusive or misleading here).
    pub override_smoke_test: bool,
    /// `#[weakly_specified]`: the declaration leaves something to the
    /// implementer — it has `any` choices, or calls a declaration that does.
    /// Required exactly then, so that a human reviews every such function.
    pub weakly_specified: bool,
    /// `#[decreases(e, …)]` on a recursive declaration: the measure
    /// (mathematical integers, compared lexicographically).
    pub decreases: Vec<Expr>,
    pub body: Vec<Stmt>,
    /// Source positions of the `requires` attributes (parallel to `requires`).
    pub requires_spans: Vec<Span>,
    /// Index of the specification file the declaration comes from (see
    /// `parse_sources`; 0 for a single file).
    pub file: usize,
    // Raw tokens the macro needs to emit the delegation stub.
    pub vis_tokens: TokenStream,
    pub params_tokens: TokenStream,
    pub ret_tokens: Option<TokenStream>,
    /// The declaration's tokens in canonical text form (see `project::canonical`):
    /// what the report records and the macro compares.
    pub source: String,
}

impl Decl {
    /// Output names and types: the return value first, then every `&mut`
    /// parameter in order.
    pub fn outputs(&self) -> Vec<(String, RType)> {
        let mut v = Vec::new();
        if let Some((n, t)) = &self.ret {
            v.push((n.clone(), t.clone()));
        }
        for p in &self.params {
            if p.mut_ref {
                v.push((p.name.clone(), p.ty.clone()));
            }
        }
        v
    }
    /// Input names and types. A `&mut` parameter `v` uses `v_old`, with a
    /// suffix when necessary to avoid another source or generated identifier.
    pub fn inputs(&self) -> Vec<(String, RType)> {
        let mut used = self.source_names();
        self.params
            .iter()
            .map(|p| {
                let name = if p.mut_ref { fresh_name(&format!("{}_old", p.name), &mut used) } else { p.name.clone() };
                (name, p.ty.clone())
            })
            .collect()
    }
    /// Every source identifier, including binders in nested expressions. Generated
    /// names must avoid these even before the corresponding binder is in scope.
    pub(crate) fn source_names(&self) -> std::collections::HashSet<String> {
        fn collect(tokens: TokenStream, out: &mut std::collections::HashSet<String>) {
            for token in tokens {
                match token {
                    proc_macro2::TokenTree::Ident(i) => { out.insert(i.to_string()); }
                    proc_macro2::TokenTree::Group(g) => collect(g.stream(), out),
                    _ => {}
                }
            }
        }
        let mut names = std::collections::HashSet::new();
        if let Ok(tokens) = self.source.parse() {
            collect(tokens, &mut names);
        }
        names.extend(self.params.iter().map(|p| p.name.clone()));
        names.extend(self.ret.iter().map(|(n, _)| n.clone()));
        names
    }
    /// Source positions of the top-level body statements.
    pub fn body_spans(&self) -> Vec<Span> {
        self.body.iter().map(|s| s.span).collect()
    }
    /// Does the body (or an attribute) call the declaration itself?
    pub fn is_recursive(&self) -> bool {
        let n = &self.name;
        self.requires.iter().chain(self.ensures.iter()).any(|e| e.calls(n)) || self.body.iter().any(|s| s.calls(n))
    }
    /// The implementer's own choices: every `any x: T where …;` statement of
    /// the body, however deeply nested, in source order, with the names of
    /// the `for` variables enclosing each (a choice is a function of those;
    /// `some` and `match` binders are determined by the rest and do not
    /// count — a choice depending on them would be circular).
    pub fn choices(&self) -> Vec<Choice> {
        fn walk(ss: &[Stmt], under: &mut Vec<String>, out: &mut Vec<Choice>) {
            for s in ss {
                match &s.kind {
                    StmtKind::Any { name, ty, .. } => out.push(Choice { name: name.clone(), ty: ty.clone(), under: under.clone() }),
                    StmtKind::ForIn { var, body, .. } | StmtKind::ForRange { var, body, .. } => {
                        under.push(var.clone());
                        walk(body, under, out);
                        under.pop();
                    }
                    StmtKind::Some { body, .. } => walk(body, under, out),
                    StmtKind::Cases(v) => walk(v, under, out),
                    StmtKind::If { then, els, .. } => {
                        walk(then, under, out);
                        if let Some(e) = els {
                            walk(e, under, out);
                        }
                    }
                    StmtKind::Implies(_, s) => walk(std::slice::from_ref(s), under, out),
                    StmtKind::Match { arms, .. } => arms.iter().for_each(|a| walk(&a.body, under, out)),
                    StmtKind::Constraint(_) => {}
                }
            }
        }
        let mut out = Vec::new();
        walk(&self.body, &mut Vec::new(), &mut out);
        out
    }
    /// The declarations the body and attributes call, each once.
    pub fn callees(&self) -> Vec<String> {
        let mut v = Vec::new();
        for e in self.requires.iter().chain(self.ensures.iter()) {
            e.callees(&mut v);
        }
        for s in &self.body {
            s.callees(&mut v);
        }
        v.dedup();
        v
    }
    /// Does the declaration inherit ambiguity: does it call a declaration
    /// that `is_weak` (other than itself)?
    pub fn inherits_ambiguity(&self, is_weak: impl Fn(&str) -> bool) -> bool {
        self.callees().iter().any(|f| f != &self.name && is_weak(f))
    }
}

/// Reserve a Lean identifier without capturing any source or generated name.
pub(crate) fn fresh_name(base: &str, used: &mut std::collections::HashSet<String>) -> String {
    let mut name = base.to_string();
    let mut suffix = 1;
    while !used.insert(name.clone()) {
        name = format!("{base}_{suffix}");
        suffix += 1;
    }
    name
}

/// An `any x: T where …;` statement of a declaration (see `Decl::choices`).
#[derive(Clone, Debug)]
pub struct Choice {
    pub name: String,
    pub ty: RType,
    /// The `for` variables enclosing it, outermost first.
    pub under: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub span: Span,
    pub kind: StmtKind,
}

#[derive(Clone, Debug)]
pub enum StmtKind {
    Constraint(Expr),
    ForIn { var: String, seq: Expr, body: Vec<Stmt> },
    ForRange { var: String, lo: Expr, hi: Expr, body: Vec<Stmt> },
    Some { binders: Vec<(String, RType)>, body: Vec<Stmt> },
    /// `any x: T where c;` — a value the implementer chooses, within `c`,
    /// in scope for the rest of its block. A choice is an extra argument of
    /// the relation: a function of the declaration's inputs and of the
    /// `for` variables around the statement, fixed before the outputs are
    /// compared.
    Any { name: String, ty: RType, wherec: Expr },
    Cases(Vec<Stmt>),
    If { cond: Expr, then: Vec<Stmt>, els: Option<Vec<Stmt>> },
    Implies(Expr, Box<Stmt>),
    /// `match e { Enum::V(x) => { … } Enum::W { f, .. } => { … } }`
    Match { scrutinee: Expr, arms: Vec<Arm> },
}

#[derive(Clone, Debug)]
pub struct Arm {
    pub span: Span,
    pub pat: Pattern,
    pub body: Vec<Stmt>,
}

#[derive(Clone, Debug)]
pub enum Pattern {
    /// `_`
    Wild,
    /// `Enum::Variant`, `Enum::Variant(a, _)`, `Enum::Variant { f, g: h, .. }`
    Variant { enum_name: String, variant: String, fields: PatFields },
}

#[derive(Clone, Debug)]
pub enum PatFields {
    Unit,
    /// Positional binders; `None` is `_`.
    Tuple(Vec<Option<String>>),
    /// `(field, binder)` pairs, `None` for `field: _`; the bool says `..` was present.
    Struct(Vec<(String, Option<String>)>, bool),
}

impl Stmt {
    pub fn new(span: Span, kind: StmtKind) -> Stmt {
        Stmt { span, kind }
    }
    /// Does the statement mention a call to `f`?
    pub fn calls(&self, f: &str) -> bool {
        match &self.kind {
            StmtKind::Constraint(e) => e.calls(f),
            StmtKind::ForIn { seq, body, .. } => seq.calls(f) || body.iter().any(|s| s.calls(f)),
            StmtKind::ForRange { lo, hi, body, .. } => lo.calls(f) || hi.calls(f) || body.iter().any(|s| s.calls(f)),
            StmtKind::Some { body, .. } => body.iter().any(|s| s.calls(f)),
            StmtKind::Any { wherec, .. } => wherec.calls(f),
            StmtKind::Cases(v) => v.iter().any(|s| s.calls(f)),
            StmtKind::If { cond, then, els } => cond.calls(f) || then.iter().any(|s| s.calls(f)) || els.iter().flatten().any(|s| s.calls(f)),
            StmtKind::Implies(c, s) => c.calls(f) || s.calls(f),
            StmtKind::Match { scrutinee, arms } => scrutinee.calls(f) || arms.iter().any(|a| a.body.iter().any(|s| s.calls(f))),
        }
    }
    /// The names of every function the statement calls.
    pub fn callees(&self, out: &mut Vec<String>) {
        match &self.kind {
            StmtKind::Constraint(e) => e.callees(out),
            StmtKind::ForIn { seq, body, .. } => {
                seq.callees(out);
                body.iter().for_each(|s| s.callees(out));
            }
            StmtKind::ForRange { lo, hi, body, .. } => {
                lo.callees(out);
                hi.callees(out);
                body.iter().for_each(|s| s.callees(out));
            }
            StmtKind::Some { body, .. } => body.iter().for_each(|s| s.callees(out)),
            StmtKind::Any { wherec, .. } => wherec.callees(out),
            StmtKind::Cases(v) => v.iter().for_each(|s| s.callees(out)),
            StmtKind::If { cond, then, els } => {
                cond.callees(out);
                then.iter().for_each(|s| s.callees(out));
                els.iter().flatten().for_each(|s| s.callees(out));
            }
            StmtKind::Implies(c, s) => {
                c.callees(out);
                s.callees(out);
            }
            StmtKind::Match { scrutinee, arms } => {
                scrutinee.callees(out);
                arms.iter().for_each(|a| a.body.iter().for_each(|s| s.callees(out)));
            }
        }
    }
}

impl Pattern {
    /// The variables a pattern binds, in field order.
    pub fn binders(&self) -> Vec<String> {
        match self {
            Pattern::Wild => vec![],
            Pattern::Variant { fields, .. } => match fields {
                PatFields::Unit => vec![],
                PatFields::Tuple(v) => v.iter().flatten().cloned().collect(),
                PatFields::Struct(v, _) => v.iter().filter_map(|(_, b)| b.clone()).collect(),
            },
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

impl BinOp {
    pub fn is_cmp(self) -> bool {
        matches!(self, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
    }
    pub fn is_arith(self) -> bool {
        matches!(self, BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem)
    }
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub span: Span,
    pub kind: ExprKind,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Int(String),
    Bool(bool),
    /// `'a'`
    Char(char),
    /// `"text"` / `b"text"`: a byte string
    Str(Vec<u8>),
    Var(String),
    Old(String),
    Bin(BinOp, Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    Neg(Box<Expr>),
    /// `e as T` (identity on integers; `char as u32` is the code point)
    Cast(Box<Expr>, RType),
    /// Call to a `func` or `rel` declared in the specification.
    Call(String, Vec<Expr>),
    /// `Some(x)`, `None`, `Ok(x)`, `Err(e)`.
    Ctor(String, Vec<Expr>),
    /// `Enum::Variant(a, b)` / `Enum::Variant { f: a, g: b }` / `Enum::Variant`;
    /// a field name is given for the struct form.
    Variant { enum_name: String, variant: String, fields: Vec<(Option<String>, Expr)> },
    /// `e.field` of a struct, or of a struct-like enum variant bound by a pattern.
    Field(Box<Expr>, String),
    In(Box<Expr>, Box<Expr>),
    InRange(Box<Expr>, String),
    InDomain(Box<Expr>, String),
    Index(Box<Expr>, Box<Expr>),
    Slice(Box<Expr>, Box<Expr>, Box<Expr>),
    IfVal(Box<Expr>, Box<Expr>, Box<Expr>),
    Method(Box<Method>),
}

impl Expr {
    pub fn new(span: Span, kind: ExprKind) -> Expr {
        Expr { span, kind }
    }
    pub fn calls(&self, f: &str) -> bool {
        let rec = |x: &Expr| x.calls(f);
        match &self.kind {
            ExprKind::Call(g, args) => g == f || args.iter().any(rec),
            ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Char(_) | ExprKind::Str(_) | ExprKind::Var(_) | ExprKind::Old(_) => false,
            ExprKind::Bin(_, l, r) | ExprKind::In(l, r) | ExprKind::Index(l, r) => rec(l) || rec(r),
            ExprKind::InRange(x, g) | ExprKind::InDomain(x, g) => g == f || rec(x),
            ExprKind::Not(x) | ExprKind::Neg(x) | ExprKind::Cast(x, _) | ExprKind::Field(x, _) => rec(x),
            ExprKind::Ctor(_, a) => a.iter().any(rec),
            ExprKind::Variant { fields, .. } => fields.iter().any(|(_, e)| rec(e)),
            ExprKind::Slice(a, b, c) | ExprKind::IfVal(a, b, c) => rec(a) || rec(b) || rec(c),
            ExprKind::Method(m) => m.children().iter().any(|x| x.calls(f)),
        }
    }
    /// Every declaration needed to lower the expression, including `range(f)`
    /// and `domain(f)`, which refer to the generated relation/precondition.
    pub fn callees(&self, out: &mut Vec<String>) {
        let mut rec = |x: &Expr| x.callees(out);
        match &self.kind {
            ExprKind::Call(g, args) => {
                out.push(g.clone());
                args.iter().for_each(|a| a.callees(out));
            }
            ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Char(_) | ExprKind::Str(_) | ExprKind::Var(_) | ExprKind::Old(_) => {}
            ExprKind::Bin(_, l, r) | ExprKind::In(l, r) | ExprKind::Index(l, r) => {
                rec(l);
                rec(r);
            }
            ExprKind::InRange(x, g) | ExprKind::InDomain(x, g) => {
                out.push(g.clone());
                x.callees(out);
            }
            ExprKind::Not(x) | ExprKind::Neg(x) | ExprKind::Cast(x, _) | ExprKind::Field(x, _) => rec(x),
            ExprKind::Ctor(_, a) => a.iter().for_each(|x| x.callees(out)),
            ExprKind::Variant { fields, .. } => fields.iter().for_each(|(_, e)| e.callees(out)),
            ExprKind::Slice(a, b, c) | ExprKind::IfVal(a, b, c) => {
                rec(a);
                rec(b);
                rec(c);
            }
            ExprKind::Method(m) => m.children().iter().for_each(|x| x.callees(out)),
        }
    }
}

/// The std vocabulary (DESIGN.md §4).
#[derive(Clone, Debug)]
pub enum Method {
    Len(Expr),
    IsEmpty(Expr),
    Contains(Expr, Expr),
    /// `s.iter().filter(|var| pred).count()`
    Count { seq: Expr, var: String, pred: Expr },
    All { seq: Expr, var: String, pred: Expr },
    Any { seq: Expr, var: String, pred: Expr },
    Sum(Expr),
    First(Expr),
    Last(Expr),
    Abs(Expr),
    Min(Expr, Expr),
    Max(Expr, Expr),
    Pow(Expr, Expr),
    IsSome(Expr),
    IsNone(Expr),
    Unwrap(Expr),
    /// `s.windows(2).all(|w| pred)` where `pred` uses `w[0]` and `w[1]`.
    Windows2All { seq: Expr, var: String, pred: Expr },
    /// `s.as_bytes()` on a string: the identity (strings are byte sequences).
    AsBytes(Expr),
    /// `m.get(&k)` on a map: `Option<V>`.
    MapGet(Expr, Expr),
    /// `m.contains_key(&k)` on a map.
    ContainsKey(Expr, Expr),
}

impl Method {
    /// The sub-expressions, binder bodies included.
    pub fn children(&self) -> Vec<&Expr> {
        match self {
            Method::Len(x) | Method::IsEmpty(x) | Method::Sum(x) | Method::First(x) | Method::Last(x) | Method::Abs(x) | Method::IsSome(x) | Method::IsNone(x) | Method::Unwrap(x) | Method::AsBytes(x) => vec![x],
            Method::Contains(a, b) | Method::Min(a, b) | Method::Max(a, b) | Method::Pow(a, b) | Method::MapGet(a, b) | Method::ContainsKey(a, b) => vec![a, b],
            Method::Count { seq, pred, .. } | Method::All { seq, pred, .. } | Method::Any { seq, pred, .. } | Method::Windows2All { seq, pred, .. } => vec![seq, pred],
        }
    }
    /// Is the result a proposition (rather than a value)?
    pub fn is_prop(&self) -> bool {
        matches!(self, Method::IsEmpty(_) | Method::Contains(..) | Method::All { .. } | Method::Any { .. } | Method::Windows2All { .. } | Method::IsSome(_) | Method::IsNone(_) | Method::ContainsKey(..))
    }
}

// ----------------------------------------------------------- user types

/// A `struct` or `enum` declared in the specification file next to the
/// `djinn!` blocks, a `const` (its value is substituted as a literal), and
/// the file's ordinary functions, which constraints may call as *ambient*
/// functions (DESIGN.md §3): trusted Rust written by the human, denoted by
/// its Aeneas translation.
#[derive(Clone, Debug, Default)]
pub struct TypeDefs {
    /// Canonical source of types and constants, for report freshness.
    pub sources: std::collections::HashMap<String, String>,
    pub enums: std::collections::HashMap<String, EnumDef>,
    pub structs: std::collections::HashMap<String, StructDef>,
    pub consts: std::collections::HashMap<String, Const>,
    pub ambient: std::collections::HashMap<String, Ambient>,
    /// Functions of the file a constraint cannot call, with the reason.
    pub ambient_errors: std::collections::HashMap<String, String>,
}

/// An ordinary Rust function of the specification file, callable from
/// constraints: `r == helper(x)` means `helper x = ok r` in Lean.
#[derive(Clone, Debug)]
pub struct Ambient {
    pub name: String,
    pub params: Vec<(String, RType)>,
    pub ret: RType,
    pub span: Span,
    /// The item's tokens in canonical form (so that editing it marks every
    /// declaration that calls it as changed).
    pub source: String,
}

#[derive(Clone, Debug)]
pub struct EnumDef {
    pub name: String,
    pub variants: Vec<VariantDef>,
}

#[derive(Clone, Debug)]
pub struct VariantDef {
    pub name: String,
    /// Field names (`None` for tuple variants) and types, in declaration
    /// order — the order of the Lean constructor's arguments.
    pub fields: Vec<(Option<String>, RType)>,
}

#[derive(Clone, Debug)]
pub struct StructDef {
    pub name: String,
    pub fields: Vec<(String, RType)>,
}

#[derive(Clone, Debug)]
pub struct Const {
    pub name: String,
    pub ty: RType,
    /// The literal, as a specification expression.
    pub value: Expr,
}

/// A parsed specification file: its declarations and the user types.
#[derive(Clone, Debug, Default)]
pub struct Program {
    pub decls: Vec<Decl>,
    pub types: TypeDefs,
    /// Every declaration, type, constant and ambient function → the index of
    /// the specification file defining it (see `parse_sources`).
    pub origin: std::collections::HashMap<String, usize>,
}

#[derive(Debug, Clone)]
pub struct Error {
    pub span: Span,
    pub msg: String,
    /// Index of the specification file the span is in (0 for a single file).
    pub file: usize,
}

impl Error {
    pub fn new(span: Span, msg: impl Into<String>) -> Self {
        Error { span, msg: msg.into(), file: 0 }
    }
    pub fn in_file(mut self, file: usize) -> Self {
        self.file = file;
        self
    }
}

pub type Result<T> = std::result::Result<T, Error>;
