mod rise;
mod rules;
mod substitute;

use egg::*;
use crate::rise::*;
use crate::rules::*;
use std::collections::HashMap;

static mut COUNTER: u32 = 0;
fn fresh_id() -> u32 {
    unsafe {
        let c = COUNTER;
        COUNTER += 1;
        c
    }
}

fn lambda(f: impl FnOnce(&str) -> String) -> String {
    let n = fresh_id();
    let x = format!("x{}", n);
    format!("(lam {} {})", x, f(x.as_str()))
}

trait DSL {
    // f1 >> f2
    fn then<S: Into<String>>(self, other: S) -> String;
    // v |> f
    fn pipe<S: Into<String>>(self, other: S) -> String;
}

impl DSL for String {
    fn then<S: Into<String>>(self, other: S) -> String {
        let c = fresh_id();
        format!("(lam x{} (app {} (app {} (var x{}))))", c, other.into(), self, c)
    }

    fn pipe<S: Into<String>>(self, other: S) -> String {
        format!("(app {} {})", other.into(), self)
    }
}

impl DSL for &str {
    fn then<S: Into<String>>(self, other: S) -> String {
        String::from(self).then(other)
    }
    fn pipe<S: Into<String>>(self, other: S) -> String {
        String::from(self).pipe(other)
    }
}

fn expr_to_alpha_equiv_pattern(e: RecExpr<Rise>) -> Pattern<Rise> {
    use std::str::FromStr;

    println!("{}", e);
    let p = Pattern::<Rise>::from(
        expr_alpha_rename(e, ENodeOrVar::ENode,
                          |s| {
                              let s2 = format!("?{}", s.as_str());
                              ENodeOrVar::Var(Var::from_str(s2.as_str()).unwrap())
                          },
                          |s| {
                              ENodeOrVar::ENode(Rise::Symbol(s))
                          }));
    println!("{}", p);
    p
}

fn expr_fresh_alpha_rename(e: RecExpr<Rise>) -> RecExpr<Rise> {
    expr_alpha_rename(e, |r| r,
                      |s| {
                          let s2 = format!("x{}", fresh_id());
                          Rise::Symbol(s2.into())
                      },
                      |s| Rise::Symbol(s))
}

fn expr_alpha_rename<L, BS, FS>(e: RecExpr<Rise>,
                                init: impl Fn(Rise) -> L,
                                bound_symbol: BS,
                                free_symbol: FS) -> RecExpr<L>
    where L: Language, BS: Fn(Symbol) -> L, FS: Fn(Symbol) -> L
{
    let original_vec = e.as_ref();
    let mut new_vec = Vec::new();
    new_vec.extend(original_vec.iter().cloned().map(init));

    struct Env<'a, L, BS, FS> {
        original_vec: &'a [Rise],
        new_vec: &'a mut [L],
        sym_map: &'a mut HashMap<Symbol, L>,
        bound_symbol: BS,
        free_symbol: FS,
    };
    fn rec<L, BS, FS>(index: usize, env: &mut Env<L, BS, FS>)
        where L: Language, BS: Fn(Symbol) -> L, FS: Fn(Symbol) -> L
    {
        match env.original_vec[index] {
            Rise::Var(id) => rec(id.into(), env),
            Rise::App([f, e]) => {
                rec(f.into(), env);
                rec(e.into(), env);
            }
            Rise::Then([f, g]) => {
                rec(f.into(), env);
                rec(g.into(), env);
            }
            Rise::Lambda([x, e]) => {
                let s = match env.original_vec[usize::from(x)] {
                    Rise::Symbol(s) => s,
                    _ => panic!("expected symbol for lambda")
                };
                if env.sym_map.insert(s, (env.bound_symbol)(s)).is_some() {
                    panic!("symbol duplicate");
                }
                rec(x.into(), env);
                rec(e.into(), env);
            }
            Rise::Symbol(sym) => {
                env.new_vec[index] = env.sym_map.get(&sym).cloned().unwrap_or_else(|| (env.free_symbol)(sym));
            }
            Rise::Number(_) => ()
        }
    }

    rec(original_vec.len() - 1, &mut Env {
        original_vec,
        new_vec: &mut new_vec[..],
        sym_map: &mut HashMap::new(),
        bound_symbol,
        free_symbol
    });
    new_vec.into()
}

fn prove_equiv(name: &str, start_s: String, goal_s: String, rule_names: &[&str]) {
    println!();
    println!("{}", name);

    let start = start_s.parse().unwrap();
    let goal = goal_s.parse().unwrap();
    println!("starting from {}", start);

    let norm_rules = rules(&[
        /*"eta", */"beta"
    ]);
    let runner = Runner::default().with_expr(&goal).run(&norm_rules);
    let (egraph, root) = (runner.egraph, runner.roots[0]);
    struct RiseAstSize;
    impl CostFunction<Rise> for RiseAstSize {
        type Cost = usize;
        fn cost<C>(&mut self, enode: &Rise, mut costs: C) -> Self::Cost
            where
                C: FnMut(Id) -> Self::Cost,
        {
            match enode {
                Rise::Symbol(s) => if s.as_str().starts_with("_") { std::usize::MAX } else { 1 }
                _ => enode.fold(1, |sum, id| sum.saturating_add(costs(id)))
            }
        }
    }
    let mut extractor = Extractor::new(&egraph, RiseAstSize);
    let (_, goal) = extractor.find_best(root);

    let rules_to_goal = rules(rule_names);
    let goal = expr_to_alpha_equiv_pattern(goal);
    let goals: Vec<Pattern<Rise>> = vec![goal];
    let mut runner = Runner::default()
        .with_expr(&start);
    
    // NOTE this is a bit of hack, we rely on the fact that the
    // initial root is the last expr added by the runner. We can't
    // use egraph.find_expr(start) because it may have been pruned
    // away
    let id = runner.egraph.find(*runner.roots.last().unwrap());

    let goals2 = goals.clone();
    runner = runner
        .with_node_limit(100_000)
        .with_iter_limit(20)
        .with_time_limit(std::time::Duration::from_secs(60))
        .with_hook(move |r| {
            if goals2.iter().all(|g| g.search_eclass(&r.egraph, id).is_some()) {
                Err("Done".into())
            } else {
                Ok(())
            }
        }).run(&rules_to_goal);
    runner.print_report();
    // runner.egraph.dot().to_svg(format!("/tmp/{}.svg", name)).unwrap();
    runner.egraph.check_goals(id, &goals);
}

fn main() {/*
    let e =
        "(app map (app (app padClamp 1) 1))".then(
        "(app (app padClamp 1) 1)".then(
        "next"));
    prove_equiv("trivial", e.clone(), e, &["eta", "beta"]);

    prove_equiv("simple beta reduction",
        "(app (lam x (app map (var x))) f)".into(),
        "(app map f)".into(),
        &["eta", "beta"]
    );

    let fissioned = "(app map (var f1))".then("(app map (var f2))").then("(app map (var f3))").then("(app map (var f4))");
    let half_fused = format!("(app map {})", "(var f1)".then("(var f2)")).then(format!("(app map {})", "(var f3)".then("(var f4)")));
    let fused = format!("(app map {})", "(var f1)".then("(var f2)").then("(var f3)").then("(var f4)"));
    let fission_fusion_rules = &["eta", "beta", "map-fusion", "map-fission"];
    prove_equiv("simple map fusion", fissioned.clone(), half_fused.clone(), fission_fusion_rules);
    prove_equiv("simple map fission", fused.clone(), fissioned, fission_fusion_rules);
    prove_equiv("map fission + map fusion", fused, half_fused, fission_fusion_rules);

    let simpler_half_fused = "(app map (var f2))".then(format!("(app map {})", "(var f3)".then("(var f4)")));
    let simpler_fused = format!("(app map {})", "(var f2)".then("(var f3)").then("(var f4)"));
    prove_equiv("simpler map fission + map fusion", simpler_fused, simpler_half_fused, fission_fusion_rules);

    let then_half_fused = "(>> (app map (>> (var f1) (var f2))) (app map (>> (var f3) (var f4))))".into();
    let then_fused = "(app map (>> (var f1) (>> (var f2) (>> (var f3) (var f4)))))".into();
    prove_equiv("then map fission + map fusion", then_fused, then_half_fused,
                &["map-fusion-then", "map-fission-then", "then-assoc-1", "then-assoc-2"]);
*/
    let tmp = "(app map (app (app slide 3) 1))".then("(app (app slide 3) 1)").then("(app map transpose)");
    let slide2d_3_1 = tmp.as_str();
    let tmp = format!("(lam a (lam b {}))", "(app (app zip (var a)) (var b))".pipe("(app map mulT)").pipe("(app (app reduce add) 0)"));
    let dot = tmp.as_str();
    let dot2: String = format!("{}", expr_fresh_alpha_rename(dot.parse().unwrap()));
    let base = slide2d_3_1.then(format!(
        "(app map (app map (lam nbh (app (app {} (app join weights2d)) (app join (var nbh))))))", dot));
    let factorised = slide2d_3_1.then(format!(
        "(app map (app map {}))", format!("(app map (app {} weightsH))", dot).then(format!("(app {} weightsV)", dot2))
    ));
    let factorisedVH = slide2d_3_1.then(format!(
        "(app map (app map {}))", "transpose".then(format!("(app map (app {} weightsV))", dot)).then(format!("(app {} weightsH)", dot2))
    ));
    let scanline = "(app (app slide 3) 1)".then(format!(
        "(app map {})",
            "transpose".then(
            format!("(app map (app {} weightsV))", dot)).then(
            "(app (app slide 3) 1)").then(
            format!("(app map (app {} weightsH))", dot2))
    ));
    let separated = "(app (app slide 3) 1)".then(
        format!("(app map {})", "transpose".then(format!("(app map (app {} weightsV))", dot)))).then(
        format!("(app map {})", "(app (app slide 3) 1)".then(format!("(app map (app {} weightsH))", dot2)))
    );

    prove_equiv("base to factorised", base.clone(), factorised,
                &["eta", "beta", "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    prove_equiv("base to factorisedVH", base.clone(), factorisedVH,
                &["eta", "beta", "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    prove_equiv("scanline to separated", scanline.clone(), separated,
                &["eta", "beta", "map-fission", "map-fusion"]);

    let scanline_s1 = "(app map (app (app slide 3) 1))".then(
        "(app (app slide 3) 1)").then(
        "(app map transpose)").then(format!(
            "(app map (app map {}))",
            "transpose".then(
            format!("(app map (app {} weightsV))", dot)).then(
            format!("(app {} weightsH)", dot2))
    ));
    let scanline_s2 = "(app (app slide 3) 1)".then(
        "(app map (app map (app (app slide 3) 1)))").then(
        "(app map transpose)").then(format!(
        "(app map (app map {}))",
        "transpose".then(
            format!("(app map (app {} weightsV))", dot)).then(
            format!("(app {} weightsH)", dot2))
    ));
    let scanline_s5= "(app (app slide 3) 1)".then(format!(
        "(app map {})",
        "(app map (app (app slide 3) 1))".then(
        "transpose").then(format!(
            "(app map {})",
            "transpose".then(
            format!("(app map (app {} weightsV))", dot)).then(
            format!("(app {} weightsH)", dot2))))
    ));
    let scanline_s6= "(app (app slide 3) 1)".then(format!(
        "(app map {})",
            "transpose".then(
            "(app (app slide 3) 1)").then(format!(
            "(app map {})",
                "transpose".then("transpose").then(
                format!("(app map (app {} weightsV))", dot)).then(
                format!("(app {} weightsH)", dot2))))
    ));

    prove_equiv("base to scanline s1", base.clone(), scanline_s1.clone(), &[
        /*"eta", */"beta", "remove-transpose-pair", "map-fusion", "map-fission",
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    prove_equiv("base to scanline s2", base.clone(), scanline_s2.clone(), &[
        /*"eta", */"beta", "remove-transpose-pair", "map-fusion", "map-fission",
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    prove_equiv("base to scanline s5", base.clone(), scanline_s5.clone(), &[
        /*"eta", */"beta", "remove-transpose-pair", "map-fusion", "map-fission",
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    prove_equiv("scanline s5 to scanline s6", scanline_s5, scanline_s6.clone(), &[
        /*"eta", */"beta", "remove-transpose-pair", "map-fusion", "map-fission",
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);

    // FIXME: equivalence not proven when adding unused map fission rule
    prove_equiv("scanline s2 to scanline s6", scanline_s2, scanline_s6.clone(), &[
        /*"eta", */"beta", "remove-transpose-pair", "map-fusion", //"map-fission", NodeLimit
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    prove_equiv("scanline s1 to scanline s6", scanline_s1, scanline_s6.clone(), &[
        /*"eta", */"beta", "remove-transpose-pair", "map-fusion", //"map-fission", IterationLimit
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    prove_equiv("base to scanline s6", base.clone(), scanline_s6, &[
        /*"eta", */"beta", "remove-transpose-pair", "map-fusion", //"map-fission", IterationLimit
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);

    // FIXME: IterationLimit
    prove_equiv("base to scanline", base, scanline, &[
        "eta", "beta", "remove-transpose-pair", "map-fusion", "map-fission",
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
}
