mod rise;
mod rules;
mod substitute;
mod alpha_equiv;
mod dbrise;
mod dbrules;
mod dbsubstitute;
mod scheduler;

use egg::*;
use crate::rise::*;
use crate::dbrise::*;
use crate::rules::*;
use crate::dbrules::*;
use crate::scheduler::*;
use crate::alpha_equiv::*;
use std::collections::HashMap;
use crate::dbrise::DBRiseExpr;

static mut COUNTER: u32 = 0;
pub fn fresh_id() -> u32 {
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
    // f1 >> f2 (DB)
    fn thendb<S: Into<String>>(self, other: S) -> String;
    // v |> f
    fn pipe<S: Into<String>>(self, other: S) -> String;
}

impl DSL for String {
    fn then<S: Into<String>>(self, other: S) -> String {
        let c = fresh_id();
        format!("(lam x{} (app {} (app {} (var x{}))))", c, other.into(), self, c)
    }

    fn thendb<S: Into<String>>(self, other: S) -> String {
        format!("(lam (app {} (app {} %0)))",
                crate::dbsubstitute::shift_copy(&other.into().parse().unwrap(), true, Index(0)),
                crate::dbsubstitute::shift_copy(&self.parse().unwrap(), true, Index(0)))
    }

    fn pipe<S: Into<String>>(self, other: S) -> String {
        format!("(app {} {})", other.into(), self)
    }
}

impl DSL for &str {
    fn then<S: Into<String>>(self, other: S) -> String {
        String::from(self).then(other)
    }
    fn thendb<S: Into<String>>(self, other: S) -> String {
        String::from(self).thendb(other)
    }
    fn pipe<S: Into<String>>(self, other: S) -> String {
        String::from(self).pipe(other)
    }
}

fn normalize(e: &RecExpr<Rise>) -> RecExpr<Rise> {
    let norm_rules = rules(&[
        "eta", "beta"
    ]);
    let runner = Runner::default().with_expr(e).run(&norm_rules);
    let (egraph, root) = (runner.egraph, runner.roots[0]);
    let mut extractor = Extractor::new(&egraph, AstSize);
    let (_, normalized) = extractor.find_best(root);
    normalized
}

fn to_db_str<S: AsRef<str>>(e: S) -> String {
    format!("{}", to_db(e.as_ref().parse().unwrap()))
}

fn to_db(e: RecExpr<Rise>) -> DBRiseExpr {
    let e = e.as_ref();
    let mut r = vec![];
    rec(&mut r, e, e.len() - 1, &[]);

    fn rec(r: &mut Vec<DBRise>, expr: &[Rise], i: usize, bound: &[Symbol]) -> Id {
        match expr[i] {
            Rise::Number(n) => add(r, DBRise::Number(n)),
            Rise::Symbol(s) => add(r, DBRise::Symbol(s)),
            Rise::Var(x) => {
                let xs = unwrap_symbol(&expr[usize::from(x)]);
                let pos = bound.iter().position(|&s| s == xs)
                    .unwrap_or_else(|| panic!("{} not bound", xs));
                add(r, DBRise::Var(Index(pos as u32)))
            },
            Rise::Lambda([v, e]) => {
                let mut bound2 = vec![unwrap_symbol(&expr[usize::from(v)])];
                bound2.extend_from_slice(bound);
                let e2 = rec(r, expr, usize::from(e), &bound2[..]);
                add(r, DBRise::Lambda(e2))
            }
            Rise::App([f, e]) => {
                let f2 = rec(r, expr, usize::from(f), bound);
                let e2 = rec(r, expr, usize::from(e), bound);
                add(r, DBRise::App([f2, e2]))
            }
            Rise::Then(_) => unimplemented!()
        }
    }

    r.into()
}

fn dbnormalize(e: &DBRiseExpr) -> DBRiseExpr {
    let norm_rules = dbrules(&[
        "eta", "beta"
    ]);
    let runner = Runner::default().with_expr(e).run(&norm_rules);
    let (egraph, root) = (runner.egraph, runner.roots[0]);
    let mut extractor = Extractor::new(&egraph, AstSize);
    let (_, normalized) = extractor.find_best(root);
    normalized
}

fn prove_equiv(name: &str, start_s: String, goal_s: String, rule_names: &[&str]) {
    println!();
    println!("{}", name);

    let start = normalize(&start_s.parse().unwrap());
    let goal = normalize(&goal_s.parse().unwrap());
    println!("starting from {}", start);

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
        .with_scheduler(SimpleScheduler)
        //.with_scheduler(Scheduler::default())
        .with_node_limit(10_000_000)
        .with_iter_limit(20)
        .with_time_limit(std::time::Duration::from_secs(600)) // 10mn
        .with_hook(move |r| {
            if goals2.iter().all(|g| g.search_eclass(&r.egraph, id).is_some()) {
                Err("Done".into())
            } else {
                Ok(())
            }
        }).run(&rules_to_goal);
    runner.print_report();
    // count_alpha_equiv(&mut runner.egraph);
    // runner.egraph.dot().to_svg(format!("/tmp/{}.svg", name)).unwrap();
    runner.egraph.check_goals(id, &goals);
}

fn db_prove_equiv(name: &str, start_s: String, goal_s: String, rule_names: &[&str]) {
    println!();
    println!("{}", name);

    println!("start: {}", start_s);
    println!("goal: {}", goal_s);
    let start = dbnormalize(&start_s.parse().unwrap());
    let goal = dbnormalize(&goal_s.parse().unwrap());
    println!("normalized start: {}", start);
    println!("normalized goal: {}", goal);

    let rules_to_goal = dbrules(rule_names);
    let goals: Vec<Pattern<DBRise>> = vec![goal.as_ref().into()];
    let mut runner = Runner::default()
        .with_expr(&start);

    // NOTE this is a bit of hack, we rely on the fact that the
    // initial root is the last expr added by the runner. We can't
    // use egraph.find_expr(start) because it may have been pruned
    // away
    let id = runner.egraph.find(*runner.roots.last().unwrap());

    let goals2 = goals.clone();
    runner = runner
        .with_scheduler(SimpleScheduler)
        //.with_scheduler(Scheduler::default())
        .with_node_limit(1_000_000)
        .with_iter_limit(30)
        .with_time_limit(std::time::Duration::from_secs(600)) // 10mn
        .with_hook(move |r| {
            //r.egraph.dot().to_svg(format!("/tmp/egg{}.svg", r.iterations.len())).unwrap();
            if goals2.iter().all(|g| g.search_eclass(&r.egraph, id).is_some()) {
                Err("Done".into())
            } else {
                Ok(())
            }
        }).run(&rules_to_goal);
    runner.print_report();
    runner.iterations.iter().for_each(|i| println!("{:?}", i));
    runner.egraph.check_goals(id, &goals);
}

fn to_db_prove_equiv(name: &str, start_s: String, goal_s: String, rule_names: &[&str]) {
    db_prove_equiv(name, to_db_str(start_s), to_db_str(goal_s), rule_names)
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
    db_prove_equiv("simple beta reduction (DB)",
                "(app (lam (app map %0)) f)".into(),
                "(app map f)".into(),
                &["eta", "beta"]
    );
    db_prove_equiv("simple eta reduction (DB)",
                   "(lam (app %1 %0))".into(), "%0".into(), &[]);

    let fission_fusion_rules = &["eta", "beta", "map-fusion", "map-fission"];

    prove_equiv("map first fission",
        format!("(app map {})", "f1".then("f2").then("f3").then("f4").then("f5")),
        "(app map f1)".then(format!("(app map {})", "f2".then("f3").then("f4").then("f5"))),
        fission_fusion_rules
    );
    db_prove_equiv("map first fission (DB)",
        format!("(lam (lam (lam (lam (app map {})))))", "%3".thendb("%2").thendb("%1").thendb("%0")),
        format!("(lam (lam (lam (lam {}))))", "(app map %3)".thendb(format!("(app map {})", "%2".thendb("%1").thendb("%0")))),
        fission_fusion_rules
    );
    to_db_prove_equiv("map first fission (DB2)",
        format!("(app map {})", "f1".then("f2").then("f3").then("f4")),
        "(app map f1)".then(format!("(app map {})", "f2".then("f3").then("f4"))),
        fission_fusion_rules
    );
    prove_equiv("map first fission (then)",
                "(app map (>> f1 (>> f2 (>> f3 (>> f4 f5)))))".into(),
                "(>> (app map f1) (app map (>> f2 (>> f3 (>> f4 f5)))))".into(),
                &["map-fusion-then", "map-fission-then", "then-assoc-1", "then-assoc-2"]);
*/
/*
    let fissioned = "(app map (var f1))".then("(app map (var f2))").then("(app map (var f3))").then("(app map (var f4))");
    let half_fused = format!("(app map {})", "(var f1)".then("(var f2)")).then(format!("(app map {})", "(var f3)".then("(var f4)")));
    let fused = format!("(app map {})", "(var f1)".then("(var f2)").then("(var f3)").then("(var f4)"));
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
    // (lam mt (app (app mul (app fst (var mt))) (app snd (var mt))))
    // \mt. (app (app mul (app fst mt)) (app snd mt)))
    // \mt. (mul (fst mt) (snd mt))
    let tmp = format!("(lam a (lam b {}))", "(app (app zip (var a)) (var b))".pipe("(app map (lam mt (app (app mul (app fst (var mt))) (app snd (var mt)))))").pipe("(app (app reduce add) 0)"));
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
/*
    prove_equiv("base to factorised", base.clone(), factorised.clone(),
                &["eta", "beta", "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    to_db_prove_equiv("base to factorised (DB)", base.clone(), factorised,
                &["eta", "beta", "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    prove_equiv("base to factorisedVH", base.clone(), factorisedVH.clone(),
                &["eta", "beta", "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    to_db_prove_equiv("base to factorisedVH (DB)", base.clone(), factorisedVH,
                &["eta", "beta", "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);

    prove_equiv("scanline to separated", scanline.clone(), separated.clone(),
                &["eta", "beta", "map-fission", "map-fusion"]);
    to_db_prove_equiv("scanline to separated (DB)", scanline.clone(), separated,
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
    let scanline_s5 = "(app (app slide 3) 1)".then(format!(
        "(app map {})",
        "(app map (app (app slide 3) 1))".then(
        "transpose").then(format!(
            "(app map {})",
            "transpose".then(
            format!("(app map (app {} weightsV))", dot)).then(
            format!("(app {} weightsH)", dot2))))
    ));
    let scanline_s6 = "(app (app slide 3) 1)".then(format!(
        "(app map {})",
            "transpose".then(
            "(app (app slide 3) 1)").then(format!(
            "(app map {})",
                "transpose".then("transpose").then(
                format!("(app map (app {} weightsV))", dot)).then(
                format!("(app {} weightsH)", dot2))))
    ));
    let scanline_s7 = "(app (app slide 3) 1)".then(format!(
        "(app map {})",
            "transpose".then(
            "(app (app slide 3) 1)").then(format!(
            "(app map {})",
                format!("(app map (app {} weightsV))", dot).then(
                format!("(app {} weightsH)", dot2))))
    ));
    let scanline_s8 = "(app (app slide 3) 1)".then(format!(
        "(app map {})",
        "transpose".then(
            "(app (app slide 3) 1)").then(format!(
            "(app map {})", format!("(app map (app {} weightsV))", dot))).then(format!(
            "(app map {})", format!("(app {} weightsH)", dot2)))
    ));
    // scanline_s9 = scanline
*/
    let scanline_rules = &[
        "eta", "beta", "remove-transpose-pair", "map-fusion", "map-fission",
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"];
    /*
    prove_equiv("base to scanline s1", base.clone(), scanline_s1.clone(), scanline_rules);
    prove_equiv("base to scanline s2", base.clone(), scanline_s2.clone(), scanline_rules);
    prove_equiv("base to scanline s5", base.clone(), scanline_s5.clone(), scanline_rules);
    prove_equiv("scanline s5 to scanline s6", scanline_s5, scanline_s6.clone(), scanline_rules);

    prove_equiv("scanline s2 to scanline s6", scanline_s2, scanline_s6.clone(), scanline_rules);
    prove_equiv("scanline s1 to scanline s6", scanline_s1, scanline_s6.clone(), scanline_rules);
    prove_equiv("base to scanline s6", base.clone(), scanline_s6, scanline_rules);
    prove_equiv("base to scanline s7", base.clone(), scanline_s7.clone(),
                scanline_rules);
    prove_equiv("scanline s7 to scanline s8", scanline_s7, scanline_s8.clone(),
                scanline_rules);
    prove_equiv("base to scanline s8", base.clone(), scanline_s8,
                scanline_rules);

    // FIXME: IterationLimit
    prove_equiv("base to scanline", base, scanline, scanline_rules);
    */
    to_db_prove_equiv("base to scanline (DB)", base, scanline, scanline_rules);

    let reorder_rules = &[
        "then-assoc-1", "then-assoc-2",
        "map-fusion-then", "map-fission-then",
        "transpose-pair-after-then", "map-map-f-before-transpose-then"];

    let reorder2D_base = "(lam f (app map (app map (var f))))";

    let reorder3D_base = "(lam f (app map (app map (app map (var f)))))";
    let reorder3D_132 = "(lam f (>> (app map transpose) (>> (app map (app map (app map (var f)))) (app map transpose))))".into();
    let reorder3D_213 = "(lam f (>> transpose (>> (app map (app map (app map (var f)))) transpose)))".into();
    let reorder3D_231 = "(lam f (>> transpose (>> (app map transpose) (>> (app map (app map (app map (var f)))) (>> (app map transpose) transpose)))))".into();
    let reorder3D_321 = "(lam f (>> (app map transpose) (>> transpose (>> (app map transpose) (>> (app map (app map (app map (var f)))) (>> (app map transpose) (>> transpose (app map transpose))))))))".into();
    let reorder3D_312 = "(lam f (>> (app map transpose) (>> transpose (>> (app map (app map (app map (var f)))) (>> transpose (app map transpose))))))".into();
    prove_equiv("reorder 3D 132", reorder3D_base.into(), reorder3D_132, reorder_rules);
    prove_equiv("reorder 3D 213", reorder3D_base.into(), reorder3D_213, reorder_rules);
    prove_equiv("reorder 3D 231", reorder3D_base.into(), reorder3D_231, reorder_rules);
    prove_equiv("reorder 3D 321", reorder3D_base.into(), reorder3D_321, reorder_rules);
    prove_equiv("reorder 3D 312", reorder3D_base.into(), reorder3D_312, reorder_rules);

    let reorder4D_base = "(lam f (app map (app map (app map (app map (var f))))))";
    let reorder4D_1243 = "(lam f (>> (app map (app map transpose)) (>> (app map (app map (app map (app map (var f))))) (app map (app map transpose)))))";
    let reorder4D_1324 = "(lam f (>> (app map transpose) (>> (app map (app map (app map (app map (var f))))) (app map transpose))))";
    let reorder4D_2134 = "(lam f (>> transpose (>> (app map (app map (app map (app map (var f))))) transpose)))";
    let reorder4D_4321 = "(lam f (>> (app map (app map transpose)) (>> (app map transpose) (>> transpose (>> (app map (app map transpose)) (>> (app map transpose) (>> (app map (app map transpose)) (>> (app map (app map (app map (app map (var f))))) (>> (app map (app map transpose)) (>> (app map transpose) (>> (app map (app map transpose)) (>> transpose (>> (app map transpose) (app map (app map transpose)))))))))))))))";
    prove_equiv("reorder 4D 1243", reorder4D_base.into(), reorder4D_1243.into(), reorder_rules);
    prove_equiv("reorder 4D 1324", reorder4D_base.into(), reorder4D_1324.into(), reorder_rules);
    prove_equiv("reorder 4D 2134", reorder4D_base.into(), reorder4D_2134.into(), reorder_rules);
    // FIXME: TimeOut
    // prove_equiv("reorder 4D 4321", reorder4D_base.into(), reorder4D_4321.into(), reorder_rules);
 
    let tiling_rules = &[
        "then-assoc-1", "then-assoc-2",
        "split-join-then",
        "map-fusion-then", "map-fission-then",
        "transpose-pair-after-then", "map-map-f-before-transpose-then"];
   
    let tiling2D_1 = "(lam f (>> split (>> (app map (app map (app map (var f)))) join)))";
    let tiling2D_2 = "(lam f (app map (>> split (>> (app map (app map (var f))) join))))";
    let tiling2D_3 = "(lam f (>> split (>> (app map (app map split)) (>> (app map transpose) (>> (app map (app map (app map (app map (var f))))) (>> (app map transpose) (>> (app map (app map join)) join)))))))";
    prove_equiv("tiling 2D (1)", reorder2D_base.into(), tiling2D_1.into(), tiling_rules);
    prove_equiv("tiling 2D (2)", reorder2D_base.into(), tiling2D_2.into(), tiling_rules);
    prove_equiv("tiling 2D (3)", reorder2D_base.into(), tiling2D_3.into(), tiling_rules);
}
