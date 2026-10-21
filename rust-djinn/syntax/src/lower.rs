//! Lowering declarations to Lean propositions and obligations.

use crate::ast::*;
use crate::types::*;
use std::collections::{HashMap, HashSet};

/// What the lowering of other declarations needs to know about a callee.
#[derive(Clone, Debug)]
pub struct DeclInfo {
    pub kind: Kind,
    pub inputs: Vec<RType>,
    pub outputs: Vec<RType>,
    pub has_pre: bool,
    pub total: bool,
    /// `#[weakly_specified]`: a caller lifts its choices into its own.
    pub weakly_specified: bool,
    /// Its choices, own and lifted, as `Lowered::choices`: known once it is
    /// lowered, which is why callees are lowered before their callers.
    pub choices: Vec<(String, String)>,
}

#[derive(Clone, Debug)]
pub struct Lowered {
    pub name: String,
    pub kind: Kind,
    pub total: bool,
    /// Spec-level inputs: `(v_old, List I32)`.
    pub inputs: Vec<(String, RType)>,
    pub outputs: Vec<(String, RType)>,
    /// Implementation parameters as Aeneas sees them: `(v, Vec I32)`.
    pub impl_params: Vec<(String, RType)>,
    pub pre: Vec<String>,
    pub spec: Vec<String>,
    pub ensures: Vec<String>,
    pub wf: Vec<String>,
    /// A recursive declaration: the `#[decreases]` measures as `ℤ` terms.
    pub decreases: Vec<String>,
    /// The implementer's choices: Lean name and type. Each is a function of
    /// the inputs (in their views) and of the `for` variables around its
    /// statement (or around the call site, for a choice lifted from a weakly
    /// specified callee), into the view of its type. Extra arguments of
    /// `_body`, existentially closed in `_spec`.
    pub choices: Vec<(String, String)>,
    /// `#[weakly_specified]`.
    pub weakly_specified: bool,
    /// Does the declaration (signature or body) mention a user type, so that
    /// `Spec.lean` needs the Aeneas `Types` module?
    pub uses_types: bool,
    /// Ambient functions the declaration calls (`Spec.lean` then needs the
    /// Aeneas `Funs` module, and Charon must translate them).
    pub ambient_calls: Vec<String>,
}

#[derive(Clone)]
pub(crate) enum Cx {
    Forall(String, String),
    ForallRange(String, String, String),
    Guard(String),
    /// One obligation for every adjacent pair in a `windows(2)` predicate.
    ForallWindow(String, String, String),
    /// `match scrut with | pat => P | _ => True`
    /// scrutinee, this arm's pattern, the patterns of the arms before it,
    /// and the number of variants of the enum (a wildcard arm is emitted only
    /// while the arms so far leave some uncovered: Lean rejects a redundant one)
    MatchArm(String, String, Vec<String>, usize),
}

/// The lowering environment of one declaration.
pub(crate) struct L<'a> {
    pub(crate) decls: &'a HashMap<String, DeclInfo>,
    pub(crate) types: &'a TypeDefs,
    pub(crate) names: &'a TypeNames,
    /// variable → (Lean term, type)
    pub(crate) env: HashMap<String, (String, SType)>,
    /// `v` → `v_old` while lowering `requires`.
    pub(crate) pre_scope: bool,
    pub(crate) old_names: HashMap<String, String>,
    pub(crate) cx: Vec<Cx>,
    pub(crate) guards: Vec<String>,
    pub(crate) wf: Vec<String>,
    pub(crate) fresh: usize,
    pub(crate) used_names: HashSet<String>,
    /// The declaration being lowered, when it is recursive: conjunctions
    /// whose right side calls it are emitted as `A ∧ (A → B)` so that Lean's
    /// termination checker sees `A`.
    pub(crate) recursive: Option<String>,
    /// The declaration has choices (own `any`, or lifted from a weakly
    /// specified callee): a recursive one then calls itself through `_body`.
    pub(crate) has_choices: bool,
    /// The inputs as the arguments of every choice function: names, and
    /// view types.
    pub(crate) input_names: Vec<String>,
    pub(crate) input_tys: Vec<String>,
    /// The `for` variables in scope: Lean name and type. A choice made under
    /// them is a function of them (and of the inputs). `some` and `match`
    /// binders are determined by the rest: a choice depending on them would
    /// be circular, and unambiguous for no implementation.
    pub(crate) binders: Vec<(String, String)>,
    /// The choices met so far (see `Lowered::choices`).
    pub(crate) choices: Vec<(String, String)>,
    /// The source names bound by `any` in the blocks being lowered, for
    /// unbinding at the end of each block.
    pub(crate) any_scope: Vec<String>,
    pub(crate) uses_types: bool,
    pub(crate) ambient_calls: Vec<String>,
}

/// Placeholder in a self-call of a declaration with choices: the choice
/// functions, passed on unchanged, are all known only once the whole body
/// is lowered.
const SELF_CHOICES: &str = "⟪SELF_CHOICES⟫";

pub fn decl_info(d: &Decl) -> DeclInfo {
    DeclInfo {
        kind: d.kind,
        inputs: d.inputs().into_iter().map(|(_, t)| t).collect(),
        outputs: d.outputs().into_iter().map(|(_, t)| t).collect(),
        has_pre: !d.requires.is_empty(),
        total: d.total || d.kind == Kind::Func,
        weakly_specified: d.weakly_specified,
        choices: Vec::new(),
    }
}

pub fn lower(d: &Decl, decls: &HashMap<String, DeclInfo>, types: &TypeDefs) -> Result<Lowered> {
    lower_with(d, decls, types, &TypeNames::new())
}

pub fn lower_with(d: &Decl, decls: &HashMap<String, DeclInfo>, types: &TypeDefs, names: &TypeNames) -> Result<Lowered> {
    // ambiguity is declared, never silent: a fn that leaves a choice to the
    // implementer, or calls one that does, carries `#[weakly_specified]`,
    // and nothing else does
    let own = !d.choices().is_empty();
    let is_weak = |f: &str| decls.get(f).map(|i| i.weakly_specified).unwrap_or(false);
    let inherits = d.inherits_ambiguity(is_weak);
    if d.kind == Kind::Func && inherits && !d.weakly_specified {
        let weak = d.callees().into_iter().find(|f| is_weak(f)).unwrap_or_default();
        return Err(Error::new(d.name_span, format!("`{}` calls `{weak}`, which is weakly specified, so it inherits the implementer's choices: mark it `#[weakly_specified]`, so that a human reviews it", d.name)));
    }
    if d.weakly_specified && !own && !inherits {
        return Err(Error::new(d.name_span, format!("`{}` is marked `#[weakly_specified]` but has no `any` and calls no weakly specified fn: drop the attribute", d.name)));
    }
    let mut env = HashMap::new();
    for (n, t) in d.inputs() {
        env.insert(n.clone(), (n, SType::Of(t)));
    }
    let old_names = d.params.iter().zip(d.inputs()).filter(|(p, _)| p.mut_ref).map(|(p, (n, _))| (p.name.clone(), n)).collect();
    let mut used_names = d.source_names();
    used_names.extend(d.inputs().into_iter().map(|(n, _)| n));
    let mut l = L {
        decls,
        types,
        names,
        env,
        pre_scope: true,
        old_names,
        cx: vec![],
        guards: vec![],
        wf: vec![],
        fresh: 0,
        used_names,
        recursive: if d.is_recursive() { Some(d.name.clone()) } else { None },
        has_choices: own || (d.kind == Kind::Func && inherits),
        input_names: d.inputs().into_iter().map(|(n, _)| n).collect(),
        input_tys: d.inputs().iter().map(|(_, t)| view_type(t, names)).collect(),
        binders: Vec::new(),
        choices: Vec::new(),
        any_scope: Vec::new(),
        uses_types: d.params.iter().any(|p| p.ty.needs_code_types())
            || d.ret.as_ref().map(|(_, t)| t.needs_code_types()).unwrap_or(false)
            || d.choices().iter().any(|c| c.ty.needs_code_types()),
        ambient_calls: Vec::new(),
    };
    let mut pre = Vec::new();
    // what Rust guarantees of its values and the mathematical view does not
    // say: a `String` or a `HashMap` holds at most `usize::MAX` bytes / entries
    for (n, t) in d.inputs() {
        if matches!(t, RType::Seq(_, SeqKind::String) | RType::Map(..)) {
            pre.push(format!("({n}.length : ℤ) ≤ ((Usize.max : ℕ) : ℤ)"));
        }
    }
    for e in &d.requires {
        pre.push(l.constraint(e)?);
    }
    let mut decreases = Vec::new();
    for e in &d.decreases {
        decreases.push(l.num(e)?);
    }
    l.guards.clear();
    // outputs come into scope
    l.pre_scope = false;
    for (n, t) in d.outputs() {
        l.env.insert(n.clone(), (n, SType::Of(t)));
    }
    let mut spec = Vec::new();
    for s in &d.body {
        spec.push(l.stmt(s)?);
    }
    let mut ensures = Vec::new();
    for e in &d.ensures {
        ensures.push(l.constraint(e)?);
    }
    // a self-call of a declaration with choices passes them all on: now
    // every choice is known
    let mut wf = l.wf;
    if l.has_choices {
        let all = l.choices.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>().join(" ");
        let fill = |x: &mut String| *x = x.replace(SELF_CHOICES, &all);
        pre.iter_mut().chain(spec.iter_mut()).chain(ensures.iter_mut()).chain(wf.iter_mut()).chain(decreases.iter_mut()).for_each(fill);
    }
    Ok(Lowered {
        name: d.name.clone(),
        kind: d.kind,
        total: d.total,
        inputs: d.inputs(),
        outputs: d.outputs(),
        impl_params: d.params.iter().map(|p| (p.name.clone(), p.ty.clone())).collect(),
        pre,
        spec,
        ensures,
        wf,
        decreases,
        choices: l.choices,
        weakly_specified: d.weakly_specified,
        uses_types: l.uses_types,
        ambient_calls: l.ambient_calls,
    })
}

pub(crate) fn conj(ps: Vec<String>) -> String {
    match ps.len() {
        0 => "True".into(),
        1 => ps.into_iter().next().unwrap(),
        _ => format!("({})", ps.join(" ∧ ")),
    }
}

pub(crate) fn is_atom(s: &str) -> bool {
    if s.chars().all(|c| c.is_alphanumeric() || c == '_' || c == '\'' || c == '.') {
        return true;
    }
    // a single balanced parenthesized group counts as atomic
    if s.starts_with('(') && s.ends_with(')') {
        let mut depth = 0i32;
        for (i, c) in s.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 && i + 1 != s.len() {
                        return false;
                    }
                }
                _ => {}
            }
        }
        return depth == 0;
    }
    false
}

fn dotval(t: &str) -> String {
    if is_atom(t) {
        format!("{t}.val")
    } else {
        format!("({t}).val")
    }
}

/// A Lean `Char` literal.
pub(crate) fn char_lit(c: char) -> String {
    if c.is_ascii_alphanumeric() || (c.is_ascii_punctuation() && c != '\'' && c != '\\') || c == ' ' {
        format!("'{c}'")
    } else {
        format!("(Char.ofNat {})", c as u32)
    }
}

/// A Lean `List U8` literal for a byte string.
pub(crate) fn bytes_lit(b: &[u8]) -> String {
    if b.is_empty() {
        "([] : List U8)".into()
    } else {
        format!("[{}]", b.iter().map(|x| format!("{x}#u8")).collect::<Vec<_>>().join(", "))
    }
}

/// What the lowering needs to know about something a constraint may call: a
/// declaration of the specification, or an ambient function of the file.
#[derive(Clone)]
pub(crate) enum Callee {
    Decl(DeclInfo),
    Ambient(Ambient),
}

impl Callee {
    fn inputs(&self) -> Vec<RType> {
        match self {
            Callee::Decl(i) => i.inputs.clone(),
            Callee::Ambient(a) => a.params.iter().map(|(_, t)| t.clone()).collect(),
        }
    }
    fn outputs(&self) -> Vec<RType> {
        match self {
            Callee::Decl(i) => i.outputs.clone(),
            Callee::Ambient(a) => vec![a.ret.clone()],
        }
    }
}

impl<'a> L<'a> {
    fn fresh_name(&mut self, prefix: &str) -> String {
        let base = format!("{prefix}{}", self.fresh);
        self.fresh += 1;
        fresh_name(&base, &mut self.used_names)
    }

    /// Evaluate a closure only for elements that the iterator actually visits.
    /// Flush inside the binder so short-circuit and partial-operation guards
    /// cannot escape with an unbound closure parameter.
    fn with_element<T>(&mut self, seq: &str, var: &str, ty: SType, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        self.flush_guards();
        self.cx.push(Cx::Forall(var.to_string(), stype_lean(&ty, self.names)));
        self.cx.push(Cx::Guard(format!("{var} ∈ {seq}")));
        let result = self.with_vars(&[(var.to_string(), ty)], f);
        self.flush_guards();
        self.cx.pop();
        self.cx.pop();
        result
    }

    /// The callee named `f`, if a constraint may call it.
    pub(crate) fn callee(&self, f: &str) -> Option<Callee> {
        if let Some(i) = self.decls.get(f) {
            return Some(Callee::Decl(i.clone()));
        }
        self.types.ambient.get(f).map(|a| Callee::Ambient(a.clone()))
    }

    /// The Lean name of the Aeneas model of an ambient function.
    fn ambient_lean(&self, f: &str) -> String {
        self.names.get(&format!("fn:{f}")).cloned().unwrap_or_else(|| f.to_string())
    }

    pub(crate) fn wrap(&self, p: String) -> String {
        let mut p = p;
        for c in self.cx.iter().rev() {
            p = match c {
                Cx::Forall(x, t) => format!("∀ {x} : {t}, {p}"),
                Cx::ForallRange(i, lo, hi) => format!("∀ {i} : ℤ, {lo} ≤ {i} → {i} < {hi} → {p}"),
                Cx::Guard(g) => format!("({g}) → {p}"),
                Cx::ForallWindow(a, b, seq) => format!("List.Chain' (fun {a} {b} => {p}) {seq}"),
                Cx::MatchArm(s, pat, prev, nvariants) => {
                    // the item holds in this arm only: the earlier arms are
                    // vacuous, and so is the rest unless this arm is the `_`
                    let before: String = prev.iter().map(|q| format!("| {q} => True ")).collect();
                    if pat == "_" {
                        format!("(match {s} with {before}| _ => {p})")
                    } else if prev.len() + 1 < *nvariants {
                        format!("(match {s} with {before}| {pat} => {p} | _ => True)")
                    } else {
                        format!("(match {s} with {before}| {pat} => {p})")
                    }
                }
            };
        }
        p
    }

    pub(crate) fn flush_guards(&mut self) {
        if !self.guards.is_empty() {
            let gs: Vec<String> = self.guards.drain(..).map(|g| format!("({g})")).collect();
            let p = gs.join(" ∧ ");
            let w = self.wrap(p);
            self.wf.push(w);
        }
    }

    /// Bind names to Lean terms for the duration of `f`.
    pub(crate) fn with_env<T>(&mut self, binds: &[(String, String, SType)], f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        let mut saved = Vec::new();
        for (n, term, t) in binds {
            saved.push((n.clone(), self.env.insert(n.clone(), (term.clone(), t.clone()))));
        }
        let r = f(self);
        for (n, old) in saved {
            match old {
                Some(t) => self.env.insert(n, t),
                None => self.env.remove(&n),
            };
        }
        r
    }

    /// Bind names to themselves.
    pub(crate) fn with_vars<T>(&mut self, binds: &[(String, SType)], f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        let b: Vec<(String, String, SType)> = binds.iter().map(|(n, t)| (n.clone(), n.clone(), t.clone())).collect();
        self.with_env(&b, f)
    }

    /// `A ∧ B`, written `A ∧ (A → B)` when lowering a recursive declaration
    /// and `B` calls it (the termination checker then sees `A`).
    /// The text a self-call contains: a declaration with choices calls
    /// itself through `_body`.
    fn self_marker(&self, me: &str) -> String {
        if self.has_choices {
            format!("{me}_body ")
        } else {
            format!("{me}_spec ")
        }
    }

    fn conj_rec(&self, ps: Vec<String>) -> String {
        let Some(me) = &self.recursive else { return conj(ps) };
        let marker = self.self_marker(me);
        if ps.len() < 2 || !ps.iter().skip(1).any(|p| p.contains(&marker)) {
            return conj(ps);
        }
        // right-nested, so that every later conjunct sees the earlier ones as
        // hypotheses and each conjunct is written at most twice
        // a conjunct that itself calls the declaration is never a hypothesis:
        // Lean would embed the termination proof of that call in the
        // hypothesis's type and later rewriting of the context would fail
        let mut acc = ps[ps.len() - 1].clone();
        for p in ps[..ps.len() - 1].iter().rev() {
            acc = if acc.contains(&marker) && !p.contains(&marker) { format!("({p} ∧ ({p} → {acc}))") } else { format!("({p} ∧ {acc})") };
        }
        acc
    }

    fn calls_me(&self, p: &str) -> bool {
        self.recursive.as_ref().map(|me| p.contains(&self.self_marker(me))).unwrap_or(false)
    }

    pub(crate) fn stmts(&mut self, ss: &[Stmt]) -> Result<String> {
        let mut v = Vec::new();
        // a choice (`any`) is in scope to the end of its block
        let mark = self.any_scope.len();
        for s in ss {
            v.push(self.stmt(s)?);
        }
        for n in self.any_scope.split_off(mark) {
            self.env.remove(&n);
        }
        Ok(self.conj_rec(v))
    }

    /// A fresh choice: a function of the inputs and of the binders in scope
    /// into `ty` (a Lean type), named after `name`; returns its Lean name
    /// and the term it stands for here (the function applied).
    fn new_choice(&mut self, name: &str, ty: &str, source_name: bool) -> (String, String) {
        // distinct Lean names for choices of the same source name in
        // sibling blocks, or lifted from several calls of the same callee
        let lean = if !source_name || self.choices.iter().any(|(n, _)| n == name)
            || self.env.contains_key(name) || self.input_names.iter().any(|n| n == name)
        {
            fresh_name(name, &mut self.used_names)
        } else {
            self.used_names.insert(name.to_string());
            name.to_string()
        };
        let paren = |t: &str| if t.contains(' ') { format!("({t})") } else { t.to_string() };
        let mut fun_ty: Vec<String> = self.input_tys.iter().map(|t| paren(t)).collect();
        fun_ty.extend(self.binders.iter().map(|(_, t)| paren(t)));
        fun_ty.push(ty.to_string());
        self.choices.push((lean.clone(), fun_ty.join(" → ")));
        let args: Vec<String> = self.input_names.iter().cloned().chain(self.binders.iter().map(|(n, _)| n.clone())).collect();
        let term = if args.is_empty() { lean.clone() } else { format!("({lean} {})", args.join(" ")) };
        (lean, term)
    }

    /// `any x: T where c;` — `x` is a fresh choice function applied to the
    /// inputs and binders; only `c` remains to be stated.
    fn any_stmt(&mut self, name: &str, ty: &RType, wherec: &Expr) -> Result<String> {
        let (_, term) = self.new_choice(name, &view_type(ty, self.names), true);
        self.env.insert(name.to_string(), (term, SType::Of(ty.clone())));
        self.any_scope.push(name.to_string());
        self.constraint(wherec)
    }

    pub(crate) fn stmt(&mut self, s: &Stmt) -> Result<String> {
        let span = s.span;
        match &s.kind {
            StmtKind::Constraint(e) => self.constraint(e),
            StmtKind::ForIn { var, seq, body } => {
                let (st, ty) = self.term(seq)?;
                let elem = match &ty {
                    SType::Of(RType::Seq(e, _)) => SType::Of((**e).clone()),
                    _ => return Err(Error::new(seq.span, format!("`for {var} in ..` needs a sequence"))),
                };
                self.flush_guards();
                let et = stype_lean(&elem, self.names);
                self.cx.push(Cx::Forall(var.clone(), et.clone()));
                self.cx.push(Cx::Guard(format!("{var} ∈ {st}")));
                self.binders.push((var.clone(), et));
                let b = self.with_vars(&[(var.clone(), elem)], |l| l.stmts(body))?;
                self.flush_guards();
                self.binders.pop();
                self.cx.pop();
                self.cx.pop();
                Ok(format!("(∀ {var}, {var} ∈ {st} → {b})"))
            }
            StmtKind::ForRange { var, lo, hi, body } => {
                let lo = self.num(lo)?;
                let hi = self.num(hi)?;
                self.flush_guards();
                self.cx.push(Cx::ForallRange(var.clone(), lo.clone(), hi.clone()));
                self.binders.push((var.clone(), "ℤ".into()));
                let b = self.with_vars(&[(var.clone(), SType::Int)], |l| l.stmts(body))?;
                self.binders.pop();
                self.cx.pop();
                Ok(format!("(∀ {var} : ℤ, {lo} ≤ {var} → {var} < {hi} → {b})"))
            }
            StmtKind::Some { binders, body } => {
                let binds: Vec<(String, SType)> = binders.iter().map(|(n, t)| (n.clone(), SType::Of(t.clone()))).collect();
                let bs: Vec<String> = binders.iter().map(|(n, t)| format!("({n} : {})", view_type(t, self.names))).collect();
                // Well-formedness items inside escape universally, guarded by the
                // body (djinnc §6.5): lower the body once to obtain the guard,
                // discarding the items, then once more under the guard.
                let saved = self.wf.len();
                let saved_choices = self.choices.len();
                let saved_names = self.used_names.clone();
                let saved_fresh = self.fresh;
                let guard = self.with_vars(&binds, |l| l.stmts(body))?;
                self.wf.truncate(saved);
                // choices lifted at call sites inside: made again, under the
                // binders, by the second lowering
                self.choices.truncate(saved_choices);
                self.used_names = saved_names;
                self.fresh = saved_fresh;
                self.guards.clear();
                for (n, t) in &binds {
                    self.cx.push(Cx::Forall(n.clone(), stype_lean(t, self.names)));
                }
                self.cx.push(Cx::Guard(guard));
                let b = self.with_vars(&binds, |l| l.stmts(body))?;
                self.cx.pop();
                for _ in &binds {
                    self.cx.pop();
                }
                Ok(format!("(∃ {}, {})", bs.join(" "), b))
            }
            StmtKind::Any { name, ty, wherec } => self.any_stmt(name, ty, wherec),
            StmtKind::Cases(alts) => {
                let mut v = Vec::new();
                for a in alts {
                    v.push(self.stmt(a)?);
                }
                Ok(format!("({})", v.join(" ∨ ")))
            }
            StmtKind::If { cond, then, els } => {
                // conditions may call funcs/rels: lifted like a constraint (djinnc §6.8 closes each side)
                let c = self.constraint_inner(cond)?;
                self.flush_guards();
                self.cx.push(Cx::Guard(c.clone()));
                let t = self.stmts(then)?;
                self.cx.pop();
                match els {
                    None => Ok(format!("({c} → {t})")),
                    Some(e) => {
                        self.cx.push(Cx::Guard(format!("¬({c})")));
                        let e = self.stmts(e)?;
                        self.cx.pop();
                        Ok(format!("(({c} → {t}) ∧ (¬({c}) → {e}))"))
                    }
                }
            }
            StmtKind::Implies(c, s) => {
                let c = self.constraint_inner(c)?;
                self.flush_guards();
                self.cx.push(Cx::Guard(c.clone()));
                let b = self.stmt(s)?;
                self.cx.pop();
                Ok(format!("({c} → {b})"))
            }
            StmtKind::Match { scrutinee, arms } => self.match_stmt(scrutinee, arms, span),
        }
    }

    /// `match t { Enum::V(x) => … }` as a Lean `match` on the Aeneas inductive.
    fn match_stmt(&mut self, scrutinee: &Expr, arms: &[Arm], span: proc_macro2::Span) -> Result<String> {
        let (st, ty) = self.term(scrutinee)?;
        let ename = match &ty {
            SType::Of(RType::Named(n)) => n.clone(),
            _ => return Err(Error::new(scrutinee.span, "`match` needs a value of a user enum type")),
        };
        let edef = self.types.enums.get(&ename).cloned().ok_or_else(|| Error::new(scrutinee.span, format!("`{ename}` is not an enum declared in the specification file")))?;
        self.uses_types = true;
        self.flush_guards();
        let lean_enum = self.names.get(&ename).cloned().unwrap_or(ename.clone());
        let mut lines = Vec::new();
        let mut prev_pats: Vec<String> = Vec::new();
        let mut covered: Vec<String> = Vec::new();
        let mut has_wild = false;
        for a in arms {
            match &a.pat {
                Pattern::Wild => {
                    has_wild = true;
                    self.cx.push(Cx::MatchArm(st.clone(), "_".into(), prev_pats.clone(), edef.variants.len()));
                    let b = self.stmts(&a.body)?;
                    self.cx.pop();
                    prev_pats.push("_".into());
                    lines.push(format!("| _ => {b}"));
                }
                Pattern::Variant { enum_name, variant, fields } => {
                    if enum_name != &ename {
                        return Err(Error::new(a.span, format!("pattern of `{enum_name}` in a match on `{ename}`")));
                    }
                    let vdef = edef.variants.iter().find(|v| &v.name == variant).ok_or_else(|| Error::new(a.span, format!("`{ename}` has no variant `{variant}`")))?;
                    if covered.contains(variant) {
                        return Err(Error::new(a.span, format!("variant `{variant}` matched twice")));
                    }
                    covered.push(variant.clone());
                    // one Lean binder per field, in declaration order; the
                    // pattern's names bound to their views
                    let mut lean_binders = Vec::new();
                    let mut binds: Vec<(String, String, SType)> = Vec::new();
                    let field_names: Vec<Option<String>> = match fields {
                        PatFields::Unit => {
                            if !vdef.fields.is_empty() {
                                return Err(Error::new(a.span, format!("`{ename}::{variant}` has {} field(s); bind or ignore them", vdef.fields.len())));
                            }
                            vec![]
                        }
                        PatFields::Tuple(v) => {
                            if v.len() != vdef.fields.len() {
                                return Err(Error::new(a.span, format!("`{ename}::{variant}` has {} field(s), the pattern names {}", vdef.fields.len(), v.len())));
                            }
                            v.clone()
                        }
                        PatFields::Struct(v, dots) => {
                            let mut out = vec![None; vdef.fields.len()];
                            for (f, b) in v {
                                let i = vdef.fields.iter().position(|(n, _)| n.as_deref() == Some(f.as_str())).ok_or_else(|| Error::new(a.span, format!("`{ename}::{variant}` has no field `{f}`")))?;
                                out[i] = b.clone();
                            }
                            if !dots {
                                let missing: Vec<String> = vdef.fields.iter().filter(|(n, _)| !v.iter().any(|(f, _)| Some(f) == n.as_ref())).filter_map(|(n, _)| n.clone()).collect();
                                if !missing.is_empty() {
                                    return Err(Error::new(a.span, format!("pattern does not mention field(s) {}; add `..` to ignore them", missing.join(", "))));
                                }
                            }
                            out
                        }
                    };
                    for (k, ((_, fty), binder)) in vdef.fields.iter().zip(field_names.iter()).enumerate() {
                        match binder {
                            None => lean_binders.push("_".to_string()),
                            Some(b) => {
                                let lean = fresh_name(&format!("{b}_{k}"), &mut self.used_names);
                                lean_binders.push(lean.clone());
                                binds.push((b.clone(), view_term(&lean, fty), SType::Of(fty.clone())));
                            }
                        }
                    }
                    let pat = if lean_binders.is_empty() { format!(".{variant}") } else { format!(".{variant} {}", lean_binders.join(" ")) };
                    self.cx.push(Cx::MatchArm(st.clone(), pat.clone(), prev_pats.clone(), edef.variants.len()));
                    let b = self.with_env(&binds, |l| l.stmts(&a.body))?;
                    self.cx.pop();
                    prev_pats.push(pat.clone());
                    lines.push(format!("| {pat} => {b}"));
                }
            }
        }
        if !has_wild {
            let missing: Vec<&str> = edef.variants.iter().map(|v| v.name.as_str()).filter(|v| !covered.iter().any(|c| c == v)).collect();
            if !missing.is_empty() {
                return Err(Error::new(span, format!("non-exhaustive `match` on `{ename}`: missing {}", missing.iter().map(|m| format!("`{ename}::{m}`")).collect::<Vec<_>>().join(", "))));
            }
        }
        let _ = lean_enum;
        Ok(format!("(match {st} with {})", lines.join(" ")))
    }

    /// A top-level constraint: relational call lifting happens here.
    pub(crate) fn constraint(&mut self, e: &Expr) -> Result<String> {
        let p = self.constraint_inner(e)?;
        self.flush_guards();
        Ok(p)
    }

    pub(crate) fn constraint_inner(&mut self, e: &Expr) -> Result<String> {
        // `b == (P)` / `b != (P)` for a boolean `b`: `(b = true ↔ P)`, with `P`
        // read as a constraint (short-circuit scoping, local lifting)
        if let ExprKind::Bin(op @ (BinOp::Eq | BinOp::Ne), l, r) = &e.kind {
            if is_proplike(l) || is_proplike(r) {
                let (bside, pside) = if is_proplike(r) { (l, r) } else { (r, l) };
                let bp = self.constraint_inner(bside)?;
                self.flush_guards();
                let pp = self.constraint_inner(pside)?;
                self.flush_guards();
                let iff = format!("({bp} ↔ {pp})");
                return Ok(if *op == BinOp::Eq { iff } else { format!("¬{iff}") });
            }
        }
        // `!P`: `P` is read as a constraint, so that the scoping of `&&`, `||`
        // and `=>` inside it, and the local lifting of its relational calls,
        // are those of `P` itself; negation does not change what is defined
        if let ExprKind::Not(x) = &e.kind {
            let xp = self.constraint_inner(x)?;
            self.flush_guards();
            return Ok(format!("¬({xp})"));
        }
        // `A && B`, `A || B` and `A => B` (parsed as `!A || B`): the right operand
        // is read under the left's truth (resp. falsity), as Rust's short-circuit
        // operators are — its partial operations need only be defined there, and
        // relational calls inside it are lifted inside it, not outside the whole
        // disjunction.
        if let ExprKind::Bin(op @ (BinOp::And | BinOp::Or), l, r) = &e.kind {
            let (lp, guard, imp) = match (*op, &l.kind) {
                (BinOp::Or, ExprKind::Not(a)) => {
                    let ap = self.constraint_inner(a)?;
                    (ap.clone(), ap, true)
                }
                (BinOp::And, _) => {
                    let lp = self.constraint_inner(l)?;
                    (lp.clone(), lp, false)
                }
                _ => {
                    let lp = self.constraint_inner(l)?;
                    (lp.clone(), format!("¬({lp})"), false)
                }
            };
            self.flush_guards();
            self.cx.push(Cx::Guard(guard.clone()));
            let rp = self.constraint_inner(r)?;
            self.flush_guards();
            self.cx.pop();
            let rec = self.calls_me(&rp) && !self.calls_me(&lp);
            return Ok(if imp {
                format!("({lp} → {rp})")
            } else if *op == BinOp::And {
                if rec { format!("({lp} ∧ ({lp} → {rp}))") } else { format!("({lp} ∧ {rp})") }
            } else if rec {
                format!("({lp} ∨ (¬({lp}) → {rp}))")
            } else {
                format!("({lp} ∨ {rp})")
            });
        }
        // A value-level conditional is local to this logical operand. Split the
        // surrounding constraint before lifting calls, so neither a branch's
        // witness nor its partial-operation requirements can become unconditional.
        if let Some((cond, then_expr, else_expr)) = split_if_value(e) {
            let cp = self.constraint_inner(&cond)?;
            self.flush_guards();
            self.cx.push(Cx::Guard(cp.clone()));
            let tp = self.constraint_inner(&then_expr)?;
            self.flush_guards();
            self.cx.pop();
            self.cx.push(Cx::Guard(format!("¬({cp})")));
            let ep = self.constraint_inner(&else_expr)?;
            self.flush_guards();
            self.cx.pop();
            return Ok(format!("(({cp} → {tp}) ∧ (¬({cp}) → {ep}))"));
        }
        // f(args) == e  /  e == f(args)
        if let ExprKind::Bin(BinOp::Eq, l, r) = &e.kind {
            if let ExprKind::Call(f, args) = &l.kind {
                if self.callee(f).is_some() {
                    return self.call_eq(f, args, r, e.span);
                }
            }
            if let ExprKind::Call(f, args) = &r.kind {
                if self.callee(f).is_some() {
                    return self.call_eq(f, args, l, e.span);
                }
            }
        }
        // call in prop position with a bool output: f(args) == true
        if let ExprKind::Call(f, args) = &e.kind {
            if let Some(info) = self.callee(f) {
                if info.outputs().len() == 1 && info.outputs()[0] == RType::Bool {
                    let t = Expr::new(e.span, ExprKind::Bool(true));
                    return self.call_eq(f, args, &t, e.span);
                }
            }
        }
        // nested calls: implicit existentials
        let mut lifted = Vec::new();
        let e2 = self.lift_calls(e, &mut lifted)?;
        if lifted.is_empty() {
            return self.prop(e);
        }
        let binds = lifted_binds(&lifted);
        self.wrap_lifted(lifted, &binds, e.span, |l| l.prop(&e2))
    }

    /// `∃ v₁ …, f₁_spec … v₁ ∧ …` around a body that uses the lifted values.
    /// Well-formedness items found in the body (and in the calls' own
    /// arguments) are stated for the witnesses: under `∀ v, f_spec … v →`.
    fn wrap_lifted(&mut self, lifted: Vec<(String, String, Vec<Expr>, RType)>, binds: &[(String, SType)], span: proc_macro2::Span, body: impl FnOnce(&mut Self) -> Result<String>) -> Result<String> {
        let mut calls = Vec::new();
        let mut pushed = 0;
        for (v, f, args, t) in &lifted {
            let call = self.with_vars(binds, |l| l.spec_app(f, args, v, span))?;
            self.flush_guards();
            self.cx.push(Cx::Forall(v.clone(), view_type(t, self.names)));
            self.cx.push(Cx::Guard(call.clone()));
            pushed += 2;
            calls.push(call);
        }
        let mut s = self.with_vars(binds, body)?;
        self.flush_guards();
        for _ in 0..pushed {
            self.cx.pop();
        }
        for ((v, _, _, t), call) in lifted.iter().zip(calls).rev() {
            s = if self.calls_me(&s) && !self.calls_me(&call) { format!("(∃ {v} : {}, {call} ∧ ({call} → {s}))", view_type(t, self.names)) } else { format!("(∃ {v} : {}, {call} ∧ {s})", view_type(t, self.names)) };
        }
        Ok(s)
    }

    /// `f(args) == out` as `f_spec args out`, with calls nested in the
    /// arguments or in `out` lifted to existentials around it.
    fn call_eq(&mut self, f: &str, args: &[Expr], out: &Expr, span: proc_macro2::Span) -> Result<String> {
        let info = self.callee(f).unwrap();
        if info.outputs().len() != 1 {
            return Err(Error::new(span, format!("`{f}` has {} outputs; equating it with a tuple is not supported yet", info.outputs().len())));
        }
        let mut lifted = Vec::new();
        let mut nargs = Vec::new();
        for a in args {
            nargs.push(self.lift_calls(a, &mut lifted)?);
        }
        let nout = self.lift_calls(out, &mut lifted)?;
        let binds = lifted_binds(&lifted);
        let f = f.to_string();
        let out_ty = info.outputs()[0].clone();
        self.wrap_lifted(lifted, &binds, span, |l| {
            let (o, oty) = l.term(&nout)?;
            if oty == SType::Of(out_ty.clone()) || matches!((&oty, &out_ty), (SType::Int, RType::MathInt)) {
                return l.spec_app(&f, &nargs, &o, span);
            }
            // the output is of another type (a machine integer against a
            // mathematical one, say): name it and compare through the views
            let v = l.fresh_name("v_out");
            let eq = Expr::new(span, ExprKind::Bin(BinOp::Eq, Box::new(Expr::new(span, ExprKind::Var(v.clone()))), Box::new(nout.clone())));
            let (call, cmp) = l.with_vars(&[(v.clone(), SType::Of(out_ty.clone()))], |l| Ok((l.spec_app(&f, &nargs, &v, span)?, l.prop(&eq)?)))?;
            Ok(format!("(∃ {v} : {}, {call} ∧ {cmp})", view_type(&out_ty, l.names)))
        })
    }

    /// `f_spec a1 … an out`, plus the call-site obligation `f_pre a1 … an`;
    /// for an ambient function, `f a1 … an = ok out` over its Aeneas model.
    pub(crate) fn spec_app(&mut self, f: &str, args: &[Expr], out: &str, span: proc_macro2::Span) -> Result<String> {
        let info = self.callee(f).unwrap();
        let inputs = info.inputs();
        if args.len() != inputs.len() {
            return Err(Error::new(span, format!("`{f}` takes {} arguments, {} given", inputs.len(), args.len())));
        }
        let mut as_ = Vec::new();
        for (a, t) in args.iter().zip(&inputs) {
            as_.push(self.term_as(a, t)?);
        }
        match info {
            Callee::Decl(info) => {
                if info.has_pre {
                    self.guards.push(format!("{f}_pre {}", as_.join(" ")));
                }
                // a recursive call of a declaration with choices passes its
                // choice functions on (`_spec`, their closure, is defined
                // only after `_body`)
                if self.recursive.as_deref() == Some(f) && self.has_choices {
                    return Ok(format!("{f}_body {} {SELF_CHOICES} {}", as_.join(" "), out));
                }
                // a call of a weakly specified callee: its choices are lifted
                // into this declaration, one fresh choice per choice of the
                // callee, a function of this declaration's inputs and of the
                // `for` variables at the call site
                if info.weakly_specified {
                    if info.choices.is_empty() {
                        return Err(Error::new(span, format!("`{f}` is weakly specified and mutually recursive with this declaration; that is not supported")));
                    }
                    let mut lifted = Vec::new();
                    for (cn, ct) in info.choices.clone() {
                        let (_, term) = self.new_choice(&format!("{f}_{cn}"), &ct, false);
                        lifted.push(term);
                    }
                    return Ok(format!("{f}_body {} {} {}", as_.join(" "), lifted.join(" "), out));
                }
                Ok(format!("{f}_spec {} {}", as_.join(" "), out))
            }
            Callee::Ambient(_) => {
                if !self.ambient_calls.iter().any(|x| x == f) {
                    self.ambient_calls.push(f.to_string());
                }
                let args_s = if as_.is_empty() { String::new() } else { format!(" {}", as_.join(" ")) };
                Ok(format!("{}{args_s} = ok {out}", self.ambient_lean(f)))
            }
        }
    }

    fn lift_calls(&mut self, e: &Expr, out: &mut Vec<(String, String, Vec<Expr>, RType)>) -> Result<Expr> {
        let span = e.span;
        let mk = |k: ExprKind| Expr::new(span, k);
        macro_rules! rec {
            ($x:expr) => {
                Box::new(self.lift_calls($x, out)?)
            };
        }
        Ok(match &e.kind {
            ExprKind::Call(f, args) if self.callee(f).is_some() => {
                let info = self.callee(f).unwrap();
                if info.outputs().len() != 1 {
                    return Err(Error::new(span, format!("`{f}` must have exactly one output to be used as a value")));
                }
                let mut nargs = Vec::new();
                for a in args {
                    nargs.push(self.lift_calls(a, out)?);
                }
                let v = self.fresh_name("v_call");
                out.push((v.clone(), f.clone(), nargs, info.outputs()[0].clone()));
                mk(ExprKind::Var(v))
            }
            ExprKind::Call(f, _) => return Err(Error::new(span, self.undeclared(f))),
            ExprKind::Bin(op, l, r) => mk(ExprKind::Bin(*op, rec!(l), rec!(r))),
            ExprKind::Not(x) => mk(ExprKind::Not(rec!(x))),
            ExprKind::Neg(x) => mk(ExprKind::Neg(rec!(x))),
            ExprKind::Cast(x, t) => mk(ExprKind::Cast(rec!(x), t.clone())),
            ExprKind::Field(x, f) => mk(ExprKind::Field(rec!(x), f.clone())),
            ExprKind::Ctor(c, args) => {
                let mut v = Vec::new();
                for a in args {
                    v.push(self.lift_calls(a, out)?);
                }
                mk(ExprKind::Ctor(c.clone(), v))
            }
            ExprKind::Variant { enum_name, variant, fields } => {
                let mut v = Vec::new();
                for (n, a) in fields {
                    v.push((n.clone(), self.lift_calls(a, out)?));
                }
                mk(ExprKind::Variant { enum_name: enum_name.clone(), variant: variant.clone(), fields: v })
            }
            ExprKind::In(a, b) => mk(ExprKind::In(rec!(a), rec!(b))),
            ExprKind::InRange(a, f) => mk(ExprKind::InRange(rec!(a), f.clone())),
            ExprKind::InDomain(a, f) => mk(ExprKind::InDomain(rec!(a), f.clone())),
            ExprKind::Index(a, b) => mk(ExprKind::Index(rec!(a), rec!(b))),
            ExprKind::Slice(a, b, c) => mk(ExprKind::Slice(rec!(a), rec!(b), rec!(c))),
            ExprKind::IfVal(a, b, c) => mk(ExprKind::IfVal(rec!(a), rec!(b), rec!(c))),
            ExprKind::Method(m) => {
                // calls inside vocabulary methods are lifted too, except under binders
                let m2 = match &**m {
                    Method::Len(x) => Method::Len(*rec!(x)),
                    Method::IsEmpty(x) => Method::IsEmpty(*rec!(x)),
                    Method::Contains(a, b) => Method::Contains(*rec!(a), *rec!(b)),
                    Method::Sum(x) => Method::Sum(*rec!(x)),
                    Method::First(x) => Method::First(*rec!(x)),
                    Method::Last(x) => Method::Last(*rec!(x)),
                    Method::Abs(x) => Method::Abs(*rec!(x)),
                    Method::Min(a, b) => Method::Min(*rec!(a), *rec!(b)),
                    Method::Max(a, b) => Method::Max(*rec!(a), *rec!(b)),
                    Method::Pow(a, b) => Method::Pow(*rec!(a), *rec!(b)),
                    Method::IsSome(x) => Method::IsSome(*rec!(x)),
                    Method::IsNone(x) => Method::IsNone(*rec!(x)),
                    Method::Unwrap(x) => Method::Unwrap(*rec!(x)),
                    Method::AsBytes(x) => Method::AsBytes(*rec!(x)),
                    Method::MapGet(a, b) => Method::MapGet(*rec!(a), *rec!(b)),
                    Method::ContainsKey(a, b) => Method::ContainsKey(*rec!(a), *rec!(b)),
                    Method::Count { seq, var, pred } => Method::Count { seq: *rec!(seq), var: var.clone(), pred: pred.clone() },
                    Method::All { seq, var, pred } => Method::All { seq: *rec!(seq), var: var.clone(), pred: pred.clone() },
                    Method::Any { seq, var, pred } => Method::Any { seq: *rec!(seq), var: var.clone(), pred: pred.clone() },
                    Method::Windows2All { seq, var, pred } => Method::Windows2All { seq: *rec!(seq), var: var.clone(), pred: pred.clone() },
                };
                mk(ExprKind::Method(Box::new(m2)))
            }
            _ => e.clone(),
        })
    }

    // ------------------------------------------------------------ propositions

    pub(crate) fn prop(&mut self, e: &Expr) -> Result<String> {
        let span = e.span;
        let err = |m: String| Err(Error::new(span, m));
        Ok(match &e.kind {
            ExprKind::Bool(true) => "True".into(),
            ExprKind::Bool(false) => "False".into(),
            ExprKind::Not(x) => format!("¬({})", self.prop(x)?),
            ExprKind::Bin(BinOp::And, l, r) => format!("({} ∧ {})", self.prop(l)?, self.prop(r)?),
            ExprKind::Bin(BinOp::Or, l, r) => format!("({} ∨ {})", self.prop(l)?, self.prop(r)?),
            ExprKind::Bin(op, l, r) if matches!(op, BinOp::Eq | BinOp::Ne) && (is_proplike(l) || is_proplike(r)) => {
                // `b == (proposition)` for a boolean b: `(b = true ↔ P)`
                let (bside, pside) = if is_proplike(r) { (l, r) } else { (r, l) };
                let bp = self.prop(bside)?;
                let pp = self.prop(pside)?;
                let iff = format!("({bp} ↔ {pp})");
                if *op == BinOp::Eq { iff } else { format!("¬{iff}") }
            }
            ExprKind::Bin(op, l, r) if op.is_cmp() => {
                let (lt, lty) = self.term(l)?;
                let (rt, rty) = self.term(r)?;
                let numeric = |t: &SType| matches!(t, SType::Int) || matches!(t, SType::Of(RType::Int { .. })) || matches!(t, SType::Of(RType::MathInt));
                let is_char = |t: &SType| matches!(t, SType::Of(RType::Char));
                let (ls, rs) = if matches!(op, BinOp::Eq | BinOp::Ne) && lty == rty && !matches!(lty, SType::Int) {
                    (lt, rt)
                } else if numeric(&lty) && numeric(&rty) {
                    (self.as_num(lt, &lty), self.as_num(rt, &rty))
                } else if is_char(&lty) && is_char(&rty) {
                    (format!("({lt}.toNat : ℤ)"), format!("({rt}.toNat : ℤ)"))
                } else if matches!(op, BinOp::Eq | BinOp::Ne) {
                    (lt, rt)
                } else {
                    return err("ordering comparison on non-numeric values".into());
                };
                let sym = match op {
                    BinOp::Eq => "=",
                    BinOp::Ne => "≠",
                    BinOp::Lt => "<",
                    BinOp::Le => "≤",
                    BinOp::Gt => ">",
                    BinOp::Ge => "≥",
                    _ => unreachable!(),
                };
                format!("{ls} {sym} {rs}")
            }
            ExprKind::In(x, s) => {
                let (st, sty) = self.term(s)?;
                // the element is written at the sequence's element type: a
                // literal (or a constant) `47` in a `&[u8]` is `47#u8`
                let elem = match &sty {
                    SType::Of(RType::Seq(elem, _)) => elem.as_ref().clone(),
                    _ => return err("`in` needs a sequence on the right".into()),
                };
                let xt = self.term_as(x, &elem)?;
                format!("{xt} ∈ {st}")
            }
            ExprKind::InRange(x, f) => {
                let info = match self.decls.get(f) {
                    Some(i) => i.clone(),
                    None => return err(format!("`range({f})`: unknown function")),
                };
                if info.outputs.len() != 1 {
                    return err(format!("`range({f})`: `{f}` must have exactly one output"));
                }
                let xt = self.term_as(x, &info.outputs[0])?;
                let as_: Vec<String> = (0..info.inputs.len()).map(|i| fresh_name(&format!("a{i}"), &mut self.used_names)).collect();
                let bs: Vec<String> = as_.iter().zip(&info.inputs).map(|(a, t)| format!("({a} : {})", view_type(t, self.names))).collect();
                if bs.is_empty() {
                    format!("{f}_spec {xt}")
                } else {
                    format!("(∃ {}, {f}_spec {} {xt})", bs.join(" "), as_.join(" "))
                }
            }
            ExprKind::InDomain(x, f) => {
                let info = match self.decls.get(f) {
                    Some(i) => i.clone(),
                    None => return err(format!("`domain({f})`: unknown function")),
                };
                if info.inputs.len() != 1 {
                    return err(format!("`domain({f})`: only unary functions are supported"));
                }
                let xt = self.term_as(x, &info.inputs[0])?;
                let pre = if info.has_pre { format!("{f}_pre {xt}") } else { "True".into() };
                if info.total {
                    pre
                } else {
                    let on: Vec<String> = (0..info.outputs.len()).map(|i| fresh_name(&format!("o{i}"), &mut self.used_names)).collect();
                    let os: Vec<String> = on.iter().zip(&info.outputs).map(|(o, t)| format!("({o} : {})", view_type(t, self.names))).collect();
                    if os.is_empty() {
                        format!("({pre} ∧ {f}_spec {xt})")
                    } else {
                        format!("({pre} ∧ ∃ {}, {f}_spec {xt} {})", os.join(" "), on.join(" "))
                    }
                }
            }
            ExprKind::Method(m) => match &**m {
                Method::IsEmpty(s) => format!("({}.length : ℤ) = 0", self.listlike(s)?),
                Method::ContainsKey(m, k) => {
                    let (mt, kty) = self.map(m)?;
                    let kt = self.term_as(k, &kty)?;
                    format!("(Djinn.Vocab.mapGet {mt} {kt}).isSome = true")
                }
                Method::Contains(s, x) => {
                    let (st, et) = self.seq(s)?;
                    // the element at the sequence's element type: a literal
                    // or constant `47` in a `&[u8]` is `47#u8`
                    let xt = match &et {
                        SType::Of(rt) => self.term_as(x, &rt.clone())?,
                        _ => self.term(x)?.0,
                    };
                    format!("{xt} ∈ {st}")
                }
                Method::All { seq, var, pred } => {
                    let (st, et) = self.seq(seq)?;
                    let p = self.with_element(&st, var, et, |l| l.constraint_inner(pred))?;
                    format!("(∀ {var}, {var} ∈ {st} → {p})")
                }
                Method::Any { seq, var, pred } => {
                    let (st, et) = self.seq(seq)?;
                    let p = self.with_element(&st, var, et, |l| l.constraint_inner(pred))?;
                    format!("(∃ {var}, {var} ∈ {st} ∧ {p})")
                }
                Method::Windows2All { seq, var, pred } => {
                    let (st, et) = self.seq(seq)?;
                    self.flush_guards();
                    let a = fresh_name(&format!("{var}0"), &mut self.used_names);
                    let b = fresh_name(&format!("{var}1"), &mut self.used_names);
                    let pred2 = subst_window(pred, var, &a, &b);
                    self.cx.push(Cx::ForallWindow(a.clone(), b.clone(), st.clone()));
                    let p = self.with_vars(&[(a.clone(), et.clone()), (b.clone(), et)], |l| l.constraint_inner(&pred2))?;
                    self.flush_guards();
                    self.cx.pop();
                    format!("List.Chain' (fun {a} {b} => {p}) {st}")
                }
                Method::IsSome(o) => format!("{}.isSome = true", self.term(o)?.0),
                Method::IsNone(o) => format!("{}.isNone = true", self.term(o)?.0),
                _ => {
                    let (t, ty) = self.term(e)?;
                    return self.bool_prop(t, &ty, span);
                }
            },
            ExprKind::Call(f, _) if self.decls.contains_key(f) => {
                return err(format!("a call to `{f}` in a nested position needs the statement-level form; this is a bug in lifting"));
            }
            _ => {
                let (t, ty) = self.term(e)?;
                return self.bool_prop(t, &ty, span);
            }
        })
    }

    fn bool_prop(&self, t: String, ty: &SType, span: proc_macro2::Span) -> Result<String> {
        if *ty == SType::Of(RType::Bool) {
            Ok(format!("{t} = true"))
        } else {
            Err(Error::new(span, format!("`{t}` is not a boolean constraint")))
        }
    }

    // ------------------------------------------------------------------ terms

    pub(crate) fn as_num(&self, t: String, ty: &SType) -> String {
        match ty {
            SType::Int | SType::Of(RType::MathInt) => t,
            SType::Of(RType::Int { signed: true, .. }) => dotval(&t),
            SType::Of(RType::Int { signed: false, .. }) => format!("({} : ℤ)", dotval(&t)),
            _ => t,
        }
    }

    pub(crate) fn num(&mut self, e: &Expr) -> Result<String> {
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Int | SType::Of(RType::Int { .. }) | SType::Of(RType::MathInt) => Ok(self.as_num(t, &ty)),
            _ => Err(Error::new(e.span, format!("`{t}` is not a number"))),
        }
    }

    pub(crate) fn seq(&mut self, e: &Expr) -> Result<(String, SType)> {
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Of(RType::Seq(el, _)) => Ok((t, SType::Of(*el))),
            SType::Of(RType::Map(..)) => Err(Error::new(e.span, format!("`{t}` is a map: use `.get(&k)`, `.contains_key(&k)`, `.len()`, `.is_empty()`"))),
            _ => Err(Error::new(e.span, format!("`{t}` is not a sequence"))),
        }
    }

    /// A sequence or a map, as the list it is viewed as.
    fn listlike(&mut self, e: &Expr) -> Result<String> {
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Of(RType::Seq(..)) | SType::Of(RType::Map(..)) => Ok(t),
            _ => Err(Error::new(e.span, format!("`{t}` is not a sequence or a map"))),
        }
    }

    /// A map: its list of entries and its key type.
    fn map(&mut self, e: &Expr) -> Result<(String, RType)> {
        let (t, ty) = self.term(e)?;
        match ty {
            SType::Of(RType::Map(k, _)) => Ok((t, *k)),
            _ => Err(Error::new(e.span, format!("`{t}` is not a map (`.get(&k)` and `.contains_key(&k)` apply to `HashMap`s; a sequence is indexed with `s[i]`)"))),
        }
    }

    fn env_type_of(&mut self, e: &Expr) -> Result<RType> {
        match self.term(e)?.1 {
            SType::Of(t) => Ok(t),
            SType::Int => Ok(RType::MathInt),
        }
    }

    /// A term expected to have Rust type `t` (used for call arguments).
    pub(crate) fn term_as(&mut self, e: &Expr, t: &RType) -> Result<String> {
        let (s, ty) = self.term(e)?;
        match (&ty, t) {
            (SType::Of(RType::Seq(..)), RType::Seq(..)) => Ok(s),
            (SType::Int, RType::MathInt) | (SType::Of(RType::MathInt), RType::MathInt) => Ok(s),
            (SType::Of(RType::Int { .. }), RType::MathInt) => Ok(self.as_num(s, &ty)),
            // a literal is written as a scalar of the expected type; any other
            // mathematical integer has no canonical machine value
            (SType::Int, RType::Int { signed, bits }) if s.chars().all(|c| c.is_ascii_digit()) => {
                Ok(format!("{s}#{}{}", if *signed { "i" } else { "u" }, if *bits == 0 { "size".to_string() } else { bits.to_string() }))
            }
            (SType::Int, RType::Int { .. }) => Err(Error::new(e.span, format!("`{s}`: a machine integer is expected, got a mathematical integer (declare the parameter as `int` in a `rel`)"))),
            _ => Ok(s),
        }
    }

    /// A constant of the specification file, as a literal term.
    fn constant(&mut self, v: &str, span: proc_macro2::Span) -> Result<(String, SType)> {
        let c = self.types.consts.get(v).cloned().ok_or_else(|| {
            Error::new(span, format!("unknown constant `{v}`: constants used in specifications must be literal `const` items of the specification file"))
        })?;
        self.term(&c.value)
    }

    pub(crate) fn term(&mut self, e: &Expr) -> Result<(String, SType)> {
        let span = e.span;
        let err = |m: String| Err(Error::new(span, m));
        Ok(match &e.kind {
            ExprKind::Int(s) => (s.clone(), SType::Int),
            ExprKind::Bool(b) => (b.to_string(), SType::Of(RType::Bool)),
            ExprKind::Char(c) => (char_lit(*c), SType::Of(RType::Char)),
            ExprKind::Str(b) => (bytes_lit(b), SType::Of(RType::Seq(Box::new(RType::Int { signed: false, bits: 8 }), SeqKind::Str))),
            ExprKind::Var(v) => {
                let name = if self.pre_scope { self.old_names.get(v).unwrap_or(v) } else { v };
                match self.env.get(name) {
                    Some((t, ty)) => (t.clone(), ty.clone()),
                    None => {
                        if v.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
                            return self.constant(v, span);
                        }
                        return err(format!("unknown variable `{v}`"));
                    }
                }
            }
            ExprKind::Old(v) => {
                let name = self.old_names.get(v).ok_or_else(|| Error::new(span, format!("`old({v})`: not a `&mut` parameter")))?;
                match self.env.get(name) {
                    Some((t, ty)) => (t.clone(), ty.clone()),
                    None => return err(format!("`old({v})`: not a `&mut` parameter")),
                }
            }
            ExprKind::Neg(x) => (format!("(-{})", self.num(x)?), SType::Int),
            ExprKind::Cast(x, to) => {
                let (t, ty) = self.term(x)?;
                match (&ty, to) {
                    (SType::Int | SType::Of(RType::Int { .. }) | SType::Of(RType::MathInt), RType::Int { .. }) => (self.as_num(t, &ty), SType::Int),
                    (SType::Of(RType::Char), RType::Int { .. }) => (format!("({t}.toNat : ℤ)"), SType::Int),
                    (SType::Of(RType::Int { signed: false, bits: 8 }), RType::Char) => (format!("(Char.ofNat {t}.val)"), SType::Of(RType::Char)),
                    (SType::Int, RType::Char) => (format!("(Char.ofNat ({t}).toNat)"), SType::Of(RType::Char)),
                    _ => return err("unsupported cast: integers cast to integers (no overflow in the specification), `char as u32`, `u8 as char`".into()),
                }
            }
            ExprKind::Bin(op, l, r) if op.is_arith() => {
                let a = self.num(l)?;
                let b = self.num(r)?;
                let sym = match op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::Div => {
                        self.guards.push(format!("{b} ≠ 0"));
                        "/"
                    }
                    BinOp::Rem => {
                        self.guards.push(format!("{b} ≠ 0"));
                        "%"
                    }
                    _ => unreachable!(),
                };
                (format!("({a} {sym} {b})"), SType::Int)
            }
            ExprKind::Ctor(c, args) => {
                let mut ts = Vec::new();
                let mut tys = Vec::new();
                for a in args {
                    let (t, ty) = self.term(a)?;
                    ts.push(if is_atom(&t) { t } else { format!("({t})") });
                    tys.push(ty);
                }
                let inner = |tys: &[SType]| -> RType {
                    match tys.first() {
                        Some(SType::Of(t)) => t.clone(),
                        _ => RType::Named("_".into()),
                    }
                };
                match c.as_str() {
                    "None" => ("none".into(), SType::Of(RType::Option(Box::new(RType::Named("_".into()))))),
                    "Some" => (format!("(some {})", ts.join(" ")), SType::Of(RType::Option(Box::new(inner(&tys))))),
                    "Ok" => (format!("(.Ok {})", ts.join(" ")), SType::Of(RType::Result(Box::new(inner(&tys)), Box::new(RType::Named("_".into()))))),
                    "Err" => (format!("(.Err {})", ts.join(" ")), SType::Of(RType::Result(Box::new(RType::Named("_".into())), Box::new(inner(&tys))))),
                    _ => unreachable!(),
                }
            }
            ExprKind::Variant { enum_name, variant, fields } => {
                let edef = self.types.enums.get(enum_name).cloned().ok_or_else(|| Error::new(span, format!("`{enum_name}` is not an enum declared in the specification file")))?;
                let vdef = edef.variants.iter().find(|v| &v.name == variant).ok_or_else(|| Error::new(span, format!("`{enum_name}` has no variant `{variant}`")))?;
                self.uses_types = true;
                if fields.len() != vdef.fields.len() {
                    return err(format!("`{enum_name}::{variant}` has {} field(s), {} given", vdef.fields.len(), fields.len()));
                }
                // arguments in declaration order
                let mut ordered: Vec<Option<&Expr>> = vec![None; vdef.fields.len()];
                for (k, (fname, fe)) in fields.iter().enumerate() {
                    let i = match fname {
                        None => k,
                        Some(f) => vdef.fields.iter().position(|(n, _)| n.as_deref() == Some(f.as_str())).ok_or_else(|| Error::new(fe.span, format!("`{enum_name}::{variant}` has no field `{f}`")))?,
                    };
                    ordered[i] = Some(fe);
                }
                let mut ts = Vec::new();
                for (fe, (_, fty)) in ordered.iter().zip(&vdef.fields) {
                    let fe = fe.ok_or_else(|| Error::new(span, "a field is missing from the constructor expression"))?;
                    ts.push(self.aeneas_value(fe, fty)?);
                }
                let lean_enum = self.names.get(enum_name).cloned().unwrap_or(enum_name.clone());
                let t = if ts.is_empty() { format!("{lean_enum}.{variant}") } else { format!("({lean_enum}.{variant} {})", ts.join(" ")) };
                (t, SType::Of(RType::Named(enum_name.clone())))
            }
            ExprKind::Field(x, f) => {
                let (t, ty) = self.term(x)?;
                let sname = match &ty {
                    SType::Of(RType::Named(n)) => n.clone(),
                    _ => return err(format!("`.{f}`: field access needs a struct value")),
                };
                let sdef = self.types.structs.get(&sname).cloned().ok_or_else(|| Error::new(span, format!("`{sname}` is not a struct declared in the specification file (enum fields are bound by `match` patterns)")))?;
                let (_, fty) = sdef.fields.iter().find(|(n, _)| n == f).ok_or_else(|| Error::new(span, format!("`{sname}` has no field `{f}`")))?;
                self.uses_types = true;
                let base = if is_atom(&t) { t } else { format!("({t})") };
                (view_term(&format!("{base}.{f}"), fty), SType::Of(fty.clone()))
            }
            ExprKind::Index(s, i) => {
                let (st, et) = self.seq(s)?;
                let (it, ity) = self.term(i)?;
                let (idx, guard) = match &ity {
                    SType::Of(RType::Int { signed: false, .. }) => {
                        let v = dotval(&it);
                        (v.clone(), format!("({v} : ℤ) < ({st}.length : ℤ)"))
                    }
                    SType::Int | SType::Of(RType::Int { .. }) | SType::Of(RType::MathInt) => {
                        let n = self.as_num(it, &ity);
                        if n.chars().all(|c| c.is_ascii_digit()) {
                            // a literal index is a Nat as it stands
                            (n.clone(), format!("{n} < ({st}.length : ℤ)"))
                        } else {
                            let nn = if is_atom(&n) { n.clone() } else { format!("({n})") };
                            (format!("{nn}.toNat"), format!("0 ≤ {n} ∧ {n} < ({st}.length : ℤ)"))
                        }
                    }
                    _ => return err("index must be an integer".into()),
                };
                self.guards.push(guard);
                (format!("{st}[{idx}]!"), et)
            }
            ExprKind::Slice(s, a, b) => {
                let (st, et) = self.seq(s)?;
                let a = self.num(a)?;
                let b = self.num(b)?;
                self.guards.push(format!("0 ≤ {a} ∧ {a} ≤ {b} ∧ {b} ≤ ({st}.length : ℤ)"));
                let elem = match et {
                    SType::Of(t) => t,
                    SType::Int => unreachable!(),
                };
                // literal bounds are natural numbers as they stand
                let is_lit = |x: &str| x.chars().all(|c| c.is_ascii_digit());
                let drop = if is_lit(&a) { a.clone() } else { format!("({a}).toNat") };
                let take = match (is_lit(&a), is_lit(&b)) {
                    (true, true) => format!("({b} - {a})"),
                    (true, false) if a == "0" => format!("({b}).toNat"),
                    _ => format!("({b} - {a}).toNat"),
                };
                (format!("(({st}.drop {drop}).take {take})"), SType::Of(RType::Seq(Box::new(elem), SeqKind::Slice)))
            }
            ExprKind::IfVal(c, a, b) => {
                let cp = self.constraint_inner(c)?;
                self.flush_guards();
                self.cx.push(Cx::Guard(cp.clone()));
                let (at, aty) = self.term(a)?;
                self.flush_guards();
                self.cx.pop();
                self.cx.push(Cx::Guard(format!("¬({cp})")));
                let (bt, bty) = self.term(b)?;
                self.flush_guards();
                self.cx.pop();
                if aty == bty {
                    (format!("(if {cp} then {at} else {bt})"), aty)
                } else {
                    let an = self.as_num(at, &aty);
                    let bn = self.as_num(bt, &bty);
                    (format!("(if {cp} then {an} else {bn})"), SType::Int)
                }
            }
            ExprKind::Method(m) => match &**m {
                Method::Len(s) => (format!("({}.length : ℤ)", self.listlike(s)?), SType::Int),
                Method::MapGet(m, k) => {
                    let (mt, kty) = self.map(m)?;
                    let vty = match &self.env_type_of(m)? {
                        RType::Map(_, v) => (**v).clone(),
                        _ => unreachable!(),
                    };
                    let kt = self.term_as(k, &kty)?;
                    (format!("(Djinn.Vocab.mapGet {mt} {kt})"), SType::Of(RType::Option(Box::new(vty))))
                }
                Method::Count { seq, var, pred } => {
                    let (st, et) = self.seq(seq)?;
                    if let Some(x) = count_target(pred, var) {
                        let xt = self.with_element(&st, var, et.clone(), |l| match &et {
                            SType::Of(t) => l.term_as(&x, t),
                            _ => Ok(l.term(&x)?.0),
                        })?;
                        (format!("(List.count {xt} {st} : ℤ)"), SType::Int)
                    } else {
                        let p = self.with_element(&st, var, et, |l| l.constraint_inner(pred))?;
                        (format!("({st}.countP (fun {var} => decide ({p})) : ℤ)"), SType::Int)
                    }
                }
                Method::Sum(s) => {
                    let (st, et) = self.seq(s)?;
                    let y = self.as_num("y".into(), &et);
                    (format!("({st}.map (fun y => {y})).sum"), SType::Int)
                }
                Method::First(s) => {
                    let (st, et) = self.seq(s)?;
                    (format!("{st}.head?"), opt(et))
                }
                Method::Last(s) => {
                    let (st, et) = self.seq(s)?;
                    (format!("{st}.getLast?"), opt(et))
                }
                Method::Abs(x) => (format!("|{}|", self.num(x)?), SType::Int),
                Method::Min(a, b) => (format!("(min {} {})", self.num(a)?, self.num(b)?), SType::Int),
                Method::Max(a, b) => (format!("(max {} {})", self.num(a)?, self.num(b)?), SType::Int),
                Method::Pow(a, n) => {
                    let n = self.num(n)?;
                    self.guards.push(format!("0 ≤ {n}"));
                    (format!("({} ^ ({n}).toNat)", self.num(a)?), SType::Int)
                }
                Method::Unwrap(o) => {
                    let (ot, oty) = self.term(o)?;
                    let inner = match oty {
                        SType::Of(RType::Option(t)) => SType::Of(*t),
                        _ => return err("`.unwrap()` needs an Option".into()),
                    };
                    self.guards.push(format!("{ot}.isSome = true"));
                    (format!("{ot}.get!"), inner)
                }
                Method::AsBytes(s) => {
                    let (st, ty) = self.term(s)?;
                    match ty {
                        SType::Of(RType::Seq(e, _)) => (st, SType::Of(RType::Seq(e, SeqKind::Slice))),
                        _ => return err("`.as_bytes()` needs a string".into()),
                    }
                }
                Method::IsEmpty(_) | Method::Contains(..) | Method::All { .. } | Method::Any { .. } | Method::Windows2All { .. } | Method::IsSome(_) | Method::IsNone(_) | Method::ContainsKey(..) => {
                    return err("a boolean vocabulary method cannot be used as a value".into())
                }
            },
            ExprKind::Call(f, _) => return err(format!("`{f}` cannot appear here (relational calls are lifted at statement level)")),
            ExprKind::Not(_) | ExprKind::Bin(..) | ExprKind::In(..) | ExprKind::InRange(..) | ExprKind::InDomain(..) => {
                return err("a proposition cannot be used as a value".into())
            }
        })
    }

    /// A specification term as a value of the Aeneas type `t` (for the
    /// arguments of a user constructor, whose fields are Aeneas-typed):
    /// scalars from `ℤ` literals, sequences from lists are not expressible
    /// without a witness, so only exact types and literals are accepted.
    fn aeneas_value(&mut self, e: &Expr, t: &RType) -> Result<String> {
        let (s, ty) = self.term(e)?;
        match (&ty, t) {
            (SType::Int, RType::Int { signed, bits }) => {
                let suffix = format!("{}{}", if *signed { "i" } else { "u" }, if *bits == 0 { "size".to_string() } else { bits.to_string() });
                Ok(format!("{s}#{suffix}"))
            }
            (SType::Of(a), b) if a == b => Ok(s),
            (SType::Of(RType::Seq(..)), RType::Seq(..)) => Err(Error::new(e.span, "a sequence cannot be placed in a constructor directly; bind the value with a pattern or compare fields instead")),
            _ => Err(Error::new(e.span, "constructor argument of the wrong type")),
        }
    }
}

fn lifted_binds(lifted: &[(String, String, Vec<Expr>, RType)]) -> Vec<(String, SType)> {
    lifted.iter().map(|(v, _, _, t)| (v.clone(), SType::Of(t.clone()))).collect()
}

impl<'a> L<'a> {
    fn undeclared(&self, f: &str) -> String {
        undeclared_call(f, self.types.ambient_errors.get(f).map(|s| s.as_str()))
    }
}

/// The message for a call to something a constraint cannot call: a name the
/// file does not define, or a function of the file whose signature a
/// constraint cannot use (`reason`).
pub fn undeclared_call(f: &str, reason: Option<&str>) -> String {
    match reason {
        Some(r) => format!("`{f}` is a function of this file but a constraint cannot call it: {r}. Constraints call the specification's `fn`s and `rel`s, the vocabulary's methods, and the file's ordinary functions over scalars, `bool`, `char`, `Option`s of those and the file's own types (their meaning is their Rust code, translated by Aeneas: trusted, like the rest of this file)"),
        None => format!("`{f}` is neither a `fn` or `rel` of the specification nor a function of this file. A constraint may call the specification's own declarations, the vocabulary's methods, and the ordinary functions written in this file (trusted Rust, translated by Aeneas). If `{f}` does I/O, it belongs in a driver beside the block (DESIGN.md §7)"),
    }
}

/// An expression that denotes a proposition rather than a value.
fn is_proplike(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Bin(op, _, _) => op.is_cmp() || matches!(op, BinOp::And | BinOp::Or),
        ExprKind::Not(_) | ExprKind::In(..) | ExprKind::InRange(..) | ExprKind::InDomain(..) => true,
        ExprKind::Method(m) => m.is_prop(),
        _ => false,
    }
}

fn opt(t: SType) -> SType {
    match t {
        SType::Of(t) => SType::Of(RType::Option(Box::new(t))),
        SType::Int => SType::Int,
    }
}

pub(crate) fn stype_lean(t: &SType, names: &TypeNames) -> String {
    match t {
        SType::Int => "ℤ".into(),
        SType::Of(t) => view_type(t, names),
    }
}

/// `|y| y == x` (either side, through `*`/`&`) → `x`
fn count_target(pred: &Expr, var: &str) -> Option<Expr> {
    if let ExprKind::Bin(BinOp::Eq, l, r) = &pred.kind {
        if matches!(&l.kind, ExprKind::Var(v) if v == var) && !mentions(r, var) {
            return Some((**r).clone());
        }
        if matches!(&r.kind, ExprKind::Var(v) if v == var) && !mentions(l, var) {
            return Some((**l).clone());
        }
    }
    None
}

fn mentions(e: &Expr, var: &str) -> bool {
    match &e.kind {
        ExprKind::Method(_) => true,
        _ => e.mentions(var),
    }
}

/// Rebuild an expression by mapping its immediate children. Predicate binders
/// are traversed only when the caller explicitly requests it.
fn map_children(e: &Expr, under_binders: bool, mut f: impl FnMut(&Expr) -> Expr) -> Expr {
    let bx = |x: &Expr, f: &mut dyn FnMut(&Expr) -> Expr| Box::new(f(x));
    let kind = match &e.kind {
        ExprKind::Bin(op, a, b) => ExprKind::Bin(*op, bx(a, &mut f), bx(b, &mut f)),
        ExprKind::Not(a) => ExprKind::Not(bx(a, &mut f)),
        ExprKind::Neg(a) => ExprKind::Neg(bx(a, &mut f)),
        ExprKind::Cast(a, t) => ExprKind::Cast(bx(a, &mut f), t.clone()),
        ExprKind::Field(a, n) => ExprKind::Field(bx(a, &mut f), n.clone()),
        ExprKind::Call(n, args) => ExprKind::Call(n.clone(), args.iter().map(&mut f).collect()),
        ExprKind::Ctor(n, args) => ExprKind::Ctor(n.clone(), args.iter().map(&mut f).collect()),
        ExprKind::Variant { enum_name, variant, fields } => ExprKind::Variant {
            enum_name: enum_name.clone(), variant: variant.clone(),
            fields: fields.iter().map(|(n, x)| (n.clone(), f(x))).collect(),
        },
        ExprKind::In(a, b) => ExprKind::In(bx(a, &mut f), bx(b, &mut f)),
        ExprKind::InRange(a, n) => ExprKind::InRange(bx(a, &mut f), n.clone()),
        ExprKind::InDomain(a, n) => ExprKind::InDomain(bx(a, &mut f), n.clone()),
        ExprKind::Index(a, b) => ExprKind::Index(bx(a, &mut f), bx(b, &mut f)),
        ExprKind::Slice(a, b, c) => ExprKind::Slice(bx(a, &mut f), bx(b, &mut f), bx(c, &mut f)),
        ExprKind::IfVal(a, b, c) => ExprKind::IfVal(bx(a, &mut f), bx(b, &mut f), bx(c, &mut f)),
        ExprKind::Method(m) => ExprKind::Method(Box::new(match &**m {
            Method::Len(a) => Method::Len(f(a)),
            Method::IsEmpty(a) => Method::IsEmpty(f(a)),
            Method::Contains(a, b) => Method::Contains(f(a), f(b)),
            Method::Sum(a) => Method::Sum(f(a)),
            Method::First(a) => Method::First(f(a)),
            Method::Last(a) => Method::Last(f(a)),
            Method::Abs(a) => Method::Abs(f(a)),
            Method::Min(a, b) => Method::Min(f(a), f(b)),
            Method::Max(a, b) => Method::Max(f(a), f(b)),
            Method::Pow(a, b) => Method::Pow(f(a), f(b)),
            Method::IsSome(a) => Method::IsSome(f(a)),
            Method::IsNone(a) => Method::IsNone(f(a)),
            Method::Unwrap(a) => Method::Unwrap(f(a)),
            Method::AsBytes(a) => Method::AsBytes(f(a)),
            Method::MapGet(a, b) => Method::MapGet(f(a), f(b)),
            Method::ContainsKey(a, b) => Method::ContainsKey(f(a), f(b)),
            Method::Count { seq, var, pred } => Method::Count { seq: f(seq), var: var.clone(), pred: if under_binders { f(pred) } else { pred.clone() } },
            Method::All { seq, var, pred } => Method::All { seq: f(seq), var: var.clone(), pred: if under_binders { f(pred) } else { pred.clone() } },
            Method::Any { seq, var, pred } => Method::Any { seq: f(seq), var: var.clone(), pred: if under_binders { f(pred) } else { pred.clone() } },
            Method::Windows2All { seq, var, pred } => Method::Windows2All { seq: f(seq), var: var.clone(), pred: if under_binders { f(pred) } else { pred.clone() } },
        })),
        _ => return e.clone(),
    };
    Expr::new(e.span, kind)
}

/// The first conditional outside predicate binders, together with the enclosing
/// expression with that occurrence replaced by each alternative.
fn split_if_value(e: &Expr) -> Option<(Expr, Expr, Expr)> {
    if let ExprKind::IfVal(c, a, b) = &e.kind {
        return Some(((**c).clone(), (**a).clone(), (**b).clone()));
    }
    let mut found = None;
    let mut child_index = 0;
    let then_expr = map_children(e, false, |child| {
        let index = child_index;
        child_index += 1;
        if found.is_none() {
            if let Some((cond, then_child, else_child)) = split_if_value(child) {
                found = Some((index, cond, else_child));
                return then_child;
            }
        }
        child.clone()
    });
    let (target, cond, else_child) = found?;
    let mut child_index = 0;
    let else_expr = map_children(e, false, |child| {
        let index = child_index;
        child_index += 1;
        if index == target { else_child.clone() } else { child.clone() }
    });
    Some((cond, then_expr, else_expr))
}

fn subst_window(e: &Expr, w: &str, a: &str, b: &str) -> Expr {
    if let ExprKind::Index(seq, i) = &e.kind {
        if matches!(&seq.kind, ExprKind::Var(v) if v == w) {
            let replacement = match &i.kind {
                ExprKind::Int(n) if n == "0" => Some(a),
                ExprKind::Int(n) if n == "1" => Some(b),
                _ => None,
            };
            if let Some(name) = replacement {
                return Expr::new(e.span, ExprKind::Var(name.to_string()));
            }
        }
    }
    map_children(e, true, |x| subst_window(x, w, a, b))
}
