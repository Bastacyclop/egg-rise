use egg::*;
use std::collections::HashSet;

define_language! {
    enum Rise {
        "var" = Var(Id),
        "app" = App([Id; 2]),
        "lam" = Lambda([Id; 2]),
        "let" = Let([Id; 3]),

        "map" = Map,

        Symbol(Symbol),
    }
}

type RiseEGraph = EGraph<Rise, RiseAnalysis>;

#[derive(Default)]
struct RiseAnalysis;

#[derive(Debug)]
struct Data {
    free: HashSet<Id>,
}

impl Analysis<Rise> for RiseAnalysis {
    type Data = Data;

    fn merge(&self, to: &mut Data, from: Data) -> bool {
        let before_len = to.free.len();
        to.free.retain(|i| from.free.contains(i));
        let did_change = before_len != to.free.len();
        did_change
    }

    fn make(egraph: &RiseEGraph, enode: &Rise) -> Data {
        let extend = |free: &mut HashSet<Id>, i: &Id| {
            free.extend(&egraph[*i].data.free);
        };
        let mut free = HashSet::default();
        match enode {
            Rise::Var(v) => {
                free.insert(*v);
            }
            Rise::Let([v, a, b]) => {
                extend(&mut free, b);
                free.remove(v);
                extend(&mut free, a);
            }
            Rise::Lambda([v, a]) => {
                extend(&mut free, a);
                free.remove(v);
            }
            _ => {
                enode.for_each(|c| extend(&mut free, &c));
            }
        }
        Data { free }
    }
}

fn var(s: &str) -> Var {
    s.parse().unwrap()
}

fn is_not_same_var(v1: Var, v2: Var) -> impl Fn(&mut RiseEGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph.find(subst[v1]) != egraph.find(subst[v2])
}

fn contains_ident(v1: Var, v2: Var) -> impl Fn(&mut RiseEGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph[subst[v1]].data.free.contains(&subst[v2])
}

fn neg(f: impl Fn(&mut RiseEGraph, Id, &Subst) -> bool) -> impl Fn(&mut RiseEGraph, Id, &Subst) -> bool {
    move |egraph, id, subst| !f(egraph, id, subst)
}

fn rules() -> Vec<Rewrite<Rise, RiseAnalysis>> {
    vec![
        rewrite!("map-fusion";
                 "(app (app map ?f) (app (app map ?g) ?arg))" =>
                 { withFreshVar("?mfu", "(app (app map (lam ?mfu (app ?f (app ?g (var ?mfu))))) ?arg)") }),
        rewrite!("map-fission";
                 "(app map (lam ?x (app ?f ?gx)))" =>
                 { withFreshVar("?mfi", "(lam ?mfi (app (app map ?f) (app (app map (lam ?x ?gx)) (var ?mfi))))") }
                 if neg(contains_ident(var("?f"), var("?x")))),

        rewrite!("eta"; "(lam ?v (app ?f (var ?v)))" => "?f"
            if neg(contains_ident(var("?f"), var("?v")))),
        // subst rules
        rewrite!("beta";     "(app (lam ?v ?body) ?e)" => "(let ?v ?e ?body)"),
        rewrite!("let-app";  "(let ?v ?e (app ?a ?b))" => "(app (let ?v ?e ?a) (let ?v ?e ?b))"),
        rewrite!("let-var-same"; "(let ?v1 ?e (var ?v1))" => "?e"),
        rewrite!("let-var-diff"; "(let ?v1 ?e (var ?v2))" => "(var ?v2)"
            if is_not_same_var(var("?v1"), var("?v2"))),
        rewrite!("let-lam-same"; "(let ?v1 ?e (lam ?v1 ?body))" => "(lam ?v1 ?body)"),
        rewrite!("let-lam-diff";
            "(let ?v1 ?e (lam ?v2 ?body))" =>
            { CaptureAvoid {
                fresh: var("?fresh"), v2: var("?v2"), e: var("?e"),
                if_not_free: "(lam ?v2 (let ?v1 ?e ?body))".parse().unwrap(),
                if_free: "(lam ?fresh (let ?v1 ?e (let ?v2 (var ?fresh) ?body)))".parse().unwrap(),
            }}
            if is_not_same_var(var("?v1"), var("?v2"))),
        rewrite!("let-map"; "(let ?v ?e map)" => "map"),
    ]
}

struct CaptureAvoid {
    fresh: Var,
    v2: Var,
    e: Var,
    if_not_free: Pattern<Rise>,
    if_free: Pattern<Rise>,
}

impl Applier<Rise, RiseAnalysis> for CaptureAvoid {
    fn apply_one(&self, egraph: &mut RiseEGraph, eclass: Id, subst: &Subst) -> Vec<Id> {
        let e = subst[self.e];
        let v2 = subst[self.v2];
        let v2_free_in_e = egraph[e].data.free.contains(&v2);
        if v2_free_in_e {
            let mut subst = subst.clone();
            let sym = Rise::Symbol(format!("_{}", eclass).into());
            subst.insert(self.fresh, egraph.add(sym));
            self.if_free.apply_one(egraph, eclass, &subst)
        } else {
            self.if_not_free.apply_one(egraph, eclass, &subst)
        }
    }
}

fn withFreshVar(name: &str, pattern: &str) -> MakeFresh {
    MakeFresh { 
        prefix: name[1..].into(),
        fresh: var(name),
        pattern: pattern.parse().unwrap()
    }
}

struct MakeFresh {
    prefix: String,
    fresh: Var,
    pattern: Pattern<Rise>,
}

impl Applier<Rise, RiseAnalysis> for MakeFresh {
    fn apply_one(&self, egraph: &mut RiseEGraph, eclass: Id, subst: &Subst) -> Vec<Id> {
        let sym = Rise::Symbol(format!("{}{}", self.prefix, eclass).into());
        let mut subst = subst.clone();
        subst.insert(self.fresh, egraph.add(sym));
        self.pattern.apply_one(egraph, eclass, &subst)
    }
}

trait DSL {
    // f1 >> f2
    fn then<S: Into<String>>(self, other: S) -> String;
    // using patterns for alpha-equivalence
    fn thenP<S: Into<String>>(self, other: S) -> String;
}

static mut COUNTER: u32 = 0;
fn freshId() -> u32 {
    unsafe {
        let c = COUNTER;
        COUNTER += 1;
        c
    }
}

impl DSL for String {
    fn then<S: Into<String>>(self, other: S) -> String {
        let c = freshId();
        format!("(lam x{} (app {} (app {} (var x{}))))", c, other.into(), self, c)
    }

    fn thenP<S: Into<String>>(self, other: S) -> String {
        let c = freshId();
        format!("(lam ?x{} (app {} (app {} (var ?x{}))))", c, other.into(), self, c)
    }
}

impl DSL for &str {
    fn then<S: Into<String>>(self, other: S) -> String {
        String::from(self).then(other)
    }

    fn thenP<S: Into<String>>(self, other: S) -> String {
        String::from(self).thenP(other)
    }
}

fn prove_equiv(name: &str, startS: String, goalS: String) {
    println!();
    println!("{}", name);

    let start = startS.parse().unwrap();
    let goal = goalS.parse().unwrap();
    println!("starting from {}", start);

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
        .with_node_limit(40_000)
        .with_iter_limit(40)
        .with_time_limit(std::time::Duration::from_secs(60))
        .with_hook(move |r| {
            if goals2.iter().all(|g| g.search_eclass(&r.egraph, id).is_some()) {
                Err("Done".into())
            } else {
                Ok(())
            }
        }).run(&rules());
    runner.print_report();
    runner.egraph.check_goals(id, &goals);
}

fn main() {
    prove_equiv("trivial",
        "(app map (app (app padClamp 1) 1))".then(
        "(app (app padClamp 1) 1)".then(
        "next"
        )),
        "(app map (app (app padClamp 1) 1))".thenP(
        "(app (app padClamp 1) 1)".thenP(
        "next"
        ))
    );

    prove_equiv("simple beta reduction",
        "(app (lam x (app map (var x))) f)".into(),
        "(app map f)".into()
    );

    prove_equiv("simple map fusion",
        "(app map (var f1))".then("(app map (var f2))").then("(app map (var f3))").then("(app map (var f4))"),
        //"(lam ?x (app (app map (var f4)) (app (app map (var f3)) (app (app map (var f2)) (app (app map (var f1)) (var ?x))))))".into()
        format!("(app map {})", "(var f1)".thenP("(var f2)")).thenP(format!("(app map {})", "(var f3)".thenP("(var f4)")))
    );

    prove_equiv("simple map fission",
        format!("(app map {})", "(var f1)".then("(var f2)").then("(var f3)").then("(var f4)")),
        "(app map (var f1))".thenP("(app map (var f2))").thenP("(app map (var f3))").thenP("(app map (var f4))")
    );

    prove_equiv("map fusion + map fission",
        format!("(app map {})", "(var f1)".then("(var f2)").then("(var f3)").then("(var f4)")),
        format!("(app map {})", "(var f1)".thenP("(var f2)")).thenP(format!("(app map {})", "(var f3)".thenP("(var f4)")))
    );
}
