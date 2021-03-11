mod rise;
mod rules;
mod substitute;
mod alpha_equiv;
mod scheduler;

use egg::*;
use crate::rise::*;
use crate::rules::*;
use crate::scheduler::*;
use crate::alpha_equiv::*;
use std::collections::HashMap;

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
    count_alpha_equiv(&mut runner.egraph);
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
*/
    let fission_fusion_rules = &["eta", "beta", "map-fusion", "map-fission"];
    prove_equiv("map first fission",
        format!("(app map {})", "(var f1)".then("(var f2)").then("(var f3)").then("(var f4)").then("(var f5)")),
        "(app map (var f1))".then(format!("(app map {})", "(var f2)".then("(var f3)").then("(var f4)").then("(var f5)"))),
        fission_fusion_rules
    );
    panic!("TODO");

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

    let scanline_rules = &[
        "eta", "beta", "remove-transpose-pair", "map-fusion", "map-fission",
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"];
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
}
