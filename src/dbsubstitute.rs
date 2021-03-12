use egg::*;
use crate::dbrise::*;
use std::collections::HashMap;

pub fn shift_copy(expr: &DBRiseExpr, up: bool, cutoff: Index) -> DBRiseExpr {
    let mut result = expr.as_ref().to_owned();
    shift_mut(&mut result, up, cutoff);
    result.into()
}

pub fn shift_mut(expr: &mut [DBRise], up: bool, cutoff: Index) {
    rec(expr, expr.len() - 1, up, cutoff);

    fn rec(expr: &mut [DBRise], ei: usize, up: bool, cutoff: Index) {
        match expr[ei] {
            DBRise::Var(index) => if index >= cutoff {
                let index2 = Index(if up { index.0 + 1 } else { index.0 - 1 });
                expr[ei] = DBRise::Var(index2);
            }
            DBRise::Lambda(e) => {
                rec(expr, usize::from(e), up, Index(cutoff.0 + 1));
            }
            DBRise::App([f, e]) => {
                rec(expr, usize::from(f), up, cutoff);
                rec(expr, usize::from(e), up, cutoff);
            }
            DBRise::Number(_) | DBRise::Symbol(_) => ()
        }
    }
}

fn replace(expr: &[DBRise], index: Index, subs: &mut [DBRise]) -> Vec<DBRise> {
    let mut result = vec![];
    rec(&mut result, expr, expr.len() - 1, index, subs);

    fn rec(result: &mut Vec<DBRise>, expr: &[DBRise], ei: usize,
           index: Index, subs: &mut [DBRise]) -> Id {
        match expr[ei] {
            DBRise::Var(index2) =>
                if index == index2 {
                    add_expr(result, subs)
                } else {
                    add(result, DBRise::Var(index2))
                },
            DBRise::Lambda(e) => {
                shift_mut(subs, true, Index(0));
                let e2 = rec(result, expr, usize::from(e), Index(index.0 + 1), subs);
                shift_mut(subs, false, Index(0));
                add(result, DBRise::Lambda(e2))
            }
            DBRise::App([f, e]) => {
                let f2 = rec(result, expr, usize::from(f), index, subs);
                let e2 = rec(result, expr, usize::from(e), index, subs);
                add(result, DBRise::App([f2, e2]))
            }
            DBRise::Symbol(_) | DBRise::Number(_) =>
                add(result, expr[ei].clone())
        }
    }

    result
}

pub fn beta_reduce(body: &DBRiseExpr, arg: &DBRiseExpr) -> DBRiseExpr {
    let arg2 = &mut arg.as_ref().to_owned();

    shift_mut(arg2, true, Index(0));
    let mut body2 = replace(body.as_ref(), Index(0), arg2);
    shift_mut(&mut body2, false, Index(0));
    body2.into()
}

#[cfg(test)]
mod tests {
    fn check(body: &str, arg: &str, res: &str) {
        let b = &body.parse().unwrap();
        let a = &arg.parse().unwrap();
        let r = res.parse().unwrap();
        assert_eq!(super::beta_reduce(b, a), r);
    }

    #[test]
    fn beta_reduce() {
        // (λ. (λ. ((λ. (0 1)) (0 1)))) --> (λ. (λ. ((0 1) 0)))
        // (λ. (0 1)) (0 1) --> (0 1) 0
        check("(app %0 %1)", "(app %0 %1)", "(app (app %0 %1) %0)");
        // r1 = (app (lam (app "%6" (app "%5" "%0"))) "%0")
        // r2 = (app (lam (app "%6" r1)) "%0")
        // r3 = (app (lam (app "%6" r2)) %0)
        // (app map (lam (app "%6" r3)))
        // --> (app map (lam (app "%6" (app "%5" (app "%4" (app "%3" (app "%2" "%0")))))))
        check("(app %6 (app %5 %0))", "%0", "(app %5 (app %4 %0))");
        check("(app %6 (app %5 (app %4 %0)))", "%0", "(app %5 (app %4 (app %3 %0)))");
        check("(app %6 (app %5 (app %4 (app %3 %0))))", "%0", "(app %5 (app %4 (app %3 (app %2 %0))))");
    }
}