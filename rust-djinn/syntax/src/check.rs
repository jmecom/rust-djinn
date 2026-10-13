//! Static checks that need no knowledge of other declarations: variable
//! scoping and the `old(..)` discipline.

use crate::ast::*;
use std::collections::HashSet;

struct Scope {
    /// Names in scope.
    vars: HashSet<String>,
    /// Those introduced by `do x := …` (reassignable).
    assigned: HashSet<String>,
}

impl Scope {
    fn with(&self, extra: &[String]) -> Scope {
        let mut s = Scope { vars: self.vars.clone(), assigned: self.assigned.clone() };
        s.vars.extend(extra.iter().cloned());
        s
    }
}

pub fn check_scope(d: &Decl) -> Result<()> {
    let span = d.name_span;
    let mut inputs: HashSet<String> = d.params.iter().map(|p| p.name.clone()).collect();
    let muts: HashSet<String> = d.params.iter().filter(|p| p.mut_ref).map(|p| p.name.clone()).collect();
    let pre = Scope { vars: inputs.clone(), assigned: HashSet::new() };
    for e in &d.requires {
        check_expr(e, &pre, &muts, false)?;
    }
    for e in &d.decreases {
        check_expr(e, &pre, &muts, false)?;
    }
    if let Some((n, _)) = &d.ret {
        if inputs.contains(n) {
            return Err(Error::new(span, format!("output `{n}` has the same name as a parameter")));
        }
        inputs.insert(n.clone());
    }
    let full = Scope { vars: inputs, assigned: HashSet::new() };
    for e in &d.ensures {
        check_expr(e, &full, &muts, true)?;
    }
    let output = d.ret.as_ref().map(|(n, _)| n.clone());
    check_block(&d.body, &full, &muts, output.as_deref())?;
    Ok(())
}

/// Check a statement list; the scope is unchanged by it.
fn check_block(ss: &[Stmt], scope: &Scope, muts: &HashSet<String>, output: Option<&str>) -> Result<Scope> {
    let mut sc = Scope { vars: scope.vars.clone(), assigned: scope.assigned.clone() };
    for s in ss {
        sc = check_stmt(s, &sc, muts, output)?;
    }
    Ok(sc)
}

fn check_stmt(s: &Stmt, scope: &Scope, muts: &HashSet<String>, output: Option<&str>) -> Result<Scope> {
    let span = s.span;
    let same = || Ok(Scope { vars: scope.vars.clone(), assigned: scope.assigned.clone() });
    match &s.kind {
        StmtKind::Constraint(e) => {
            check_expr(e, scope, muts, true)?;
            same()
        }
        StmtKind::ForIn { var, seq, body } => {
            check_expr(seq, scope, muts, true)?;
            bind_ok(scope, var, span)?;
            check_block(body, &scope.with(&[var.clone()]), muts, output)?;
            same()
        }
        StmtKind::ForRange { var, lo, hi, body } => {
            check_expr(lo, scope, muts, true)?;
            check_expr(hi, scope, muts, true)?;
            bind_ok(scope, var, span)?;
            check_block(body, &scope.with(&[var.clone()]), muts, output)?;
            same()
        }
        StmtKind::Some { binders, body } => {
            let mut sc = scope.with(&[]);
            for (b, _) in binders {
                bind_ok(&sc, b, span)?;
                sc.vars.insert(b.clone());
            }
            check_block(body, &sc, muts, output)?;
            same()
        }
        // a choice is in scope for the rest of its block
        StmtKind::Any { name, wherec, .. } => {
            bind_ok(scope, name, span)?;
            let sc = scope.with(&[name.clone()]);
            check_expr(wherec, &sc, muts, true)?;
            Ok(sc)
        }
        StmtKind::Cases(alts) => {
            for a in alts {
                check_stmt(a, scope, muts, output)?;
            }
            same()
        }
        StmtKind::If { cond, then, els } => {
            check_expr(cond, scope, muts, true)?;
            if let Some(o) = output {
                if cond.mentions(o) {
                    return Err(Error::new(cond.span, format!("the output `{o}` may not appear in a condition")));
                }
            }
            let a = check_block(then, scope, muts, output)?;
            match els {
                Some(e) => {
                    let b = check_block(e, scope, muts, output)?;
                    // definitely assigned after the join: assigned on both paths
                    Ok(Scope { vars: a.vars.intersection(&b.vars).cloned().collect(), assigned: a.assigned.intersection(&b.assigned).cloned().collect() })
                }
                None => same(),
            }
        }
        StmtKind::Implies(c, b) => {
            check_expr(c, scope, muts, true)?;
            check_stmt(b, scope, muts, output)?;
            same()
        }
        StmtKind::Match { scrutinee, arms } => {
            check_expr(scrutinee, scope, muts, true)?;
            for a in arms {
                let mut sc = scope.with(&[]);
                if let Pattern::Variant { fields, .. } = &a.pat {
                    let binders: Vec<&String> = match fields {
                        PatFields::Unit => vec![],
                        PatFields::Tuple(v) => v.iter().flatten().collect(),
                        PatFields::Struct(v, _) => v.iter().filter_map(|(_, b)| b.as_ref()).collect(),
                    };
                    for b in binders {
                        bind_ok(&sc, b, a.span)?;
                        sc.vars.insert(b.clone());
                    }
                }
                check_block(&a.body, &sc, muts, output)?;
            }
            same()
        }
    }
}

fn bind_ok(sc: &Scope, v: &str, span: proc_macro2::Span) -> Result<()> {
    if sc.vars.contains(v) {
        return Err(Error::new(span, format!("binder `{v}` shadows a name already in scope")));
    }
    Ok(())
}

impl Expr {
    /// Does the expression mention the variable `v`?
    pub fn mentions(&self, v: &str) -> bool {
        let rec = |x: &Expr| x.mentions(v);
        match &self.kind {
            ExprKind::Var(x) | ExprKind::Old(x) => x == v,
            ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Char(_) | ExprKind::Str(_) => false,
            ExprKind::Bin(_, l, r) | ExprKind::In(l, r) | ExprKind::Index(l, r) => rec(l) || rec(r),
            ExprKind::Not(x) | ExprKind::Neg(x) | ExprKind::Cast(x, _) | ExprKind::InRange(x, _) | ExprKind::InDomain(x, _) | ExprKind::Field(x, _) => rec(x),
            ExprKind::Call(_, a) | ExprKind::Ctor(_, a) => a.iter().any(rec),
            ExprKind::Variant { fields, .. } => fields.iter().any(|(_, e)| rec(e)),
            ExprKind::Slice(a, b, c) | ExprKind::IfVal(a, b, c) => rec(a) || rec(b) || rec(c),
            ExprKind::Method(m) => m.children().iter().any(|x| x.mentions(v)),
        }
    }
}

fn check_expr(e: &Expr, scope: &Scope, muts: &HashSet<String>, old_ok: bool) -> Result<()> {
    let span = e.span;
    let rec = |x: &Expr| check_expr(x, scope, muts, old_ok);
    match &e.kind {
        ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Char(_) | ExprKind::Str(_) => Ok(()),
        ExprKind::Var(v) => {
            if scope.vars.contains(v) {
                Ok(())
            } else if v.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
                Ok(()) // a constant (checked against the file's `const` items when lowering)
            } else {
                Err(Error::new(span, format!("unknown variable `{v}`")))
            }
        }
        ExprKind::Old(v) => {
            if !muts.contains(v) {
                return Err(Error::new(span, format!("`old({v})`: `{v}` is not a `&mut` parameter")));
            }
            if !old_ok {
                return Err(Error::new(span, "`old(..)` is not allowed in `requires` (inputs are already the entry values)"));
            }
            Ok(())
        }
        ExprKind::Bin(_, l, r) | ExprKind::In(l, r) | ExprKind::Index(l, r) => {
            rec(l)?;
            rec(r)
        }
        ExprKind::Not(x) | ExprKind::Neg(x) | ExprKind::Cast(x, _) | ExprKind::InRange(x, _) | ExprKind::InDomain(x, _) | ExprKind::Field(x, _) => rec(x),
        ExprKind::Call(_, args) | ExprKind::Ctor(_, args) => args.iter().try_for_each(rec),
        ExprKind::Variant { fields, .. } => fields.iter().try_for_each(|(_, e)| rec(e)),
        ExprKind::Slice(s, a, b) => {
            rec(s)?;
            rec(a)?;
            rec(b)
        }
        ExprKind::IfVal(c, a, b) => {
            rec(c)?;
            rec(a)?;
            rec(b)
        }
        ExprKind::Method(m) => {
            let with_var = |seq: &Expr, var: &str, pred: &Expr| -> Result<()> {
                rec(seq)?;
                bind_ok(scope, var, span)?;
                check_expr(pred, &scope.with(&[var.to_string()]), muts, old_ok)
            };
            match &**m {
                Method::Count { seq, var, pred } | Method::All { seq, var, pred } | Method::Any { seq, var, pred } | Method::Windows2All { seq, var, pred } => with_var(seq, var, pred),
                other => other.children().into_iter().try_for_each(rec),
            }
        }
    }
}
