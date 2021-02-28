use egg::*;
use std::collections::{HashSet, HashMap};

define_language! {
    enum Rise {
        "var" = Var(Id),
        "app" = App([Id; 2]),
        "lam" = Lambda([Id; 2]),

        Number(i32),
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
        //to.free.extend(from.free);
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

fn contains_ident(v1: Var, v2: Var) -> impl Fn(&mut RiseEGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph[subst[v1]].data.free.contains(&subst[v2])
}

fn neg(f: impl Fn(&mut RiseEGraph, Id, &Subst) -> bool) -> impl Fn(&mut RiseEGraph, Id, &Subst) -> bool {
    move |egraph, id, subst| !f(egraph, id, subst)
}

fn rules(names: &[&str]) -> Vec<Rewrite<Rise, RiseAnalysis>> {
    let all = vec![
        // algorithmic
        rewrite!("map-fusion";
            "(app (app map ?f) (app (app map ?g) ?arg))" =>
            { with_fresh_var("?mfu", "(app (app map (lam ?mfu (app ?f (app ?g (var ?mfu))))) ?arg)") }),
        rewrite!("map-fission";
            "(app map (lam ?x (app ?f ?gx)))" =>
            { with_fresh_var("?mfi", "(lam ?mfi (app (app map ?f) (app (app map (lam ?x ?gx)) (var ?mfi))))") }
            if neg(contains_ident(var("?f"), var("?x")))),

        // reductions
        rewrite!("eta"; "(lam ?v (app ?f (var ?v)))" => "?f"
            if neg(contains_ident(var("?f"), var("?v")))),
        rewrite!("beta"; "(app (lam ?v ?body) ?e)" =>
            { BetaApplier { v: var("?v"), e: var("?e"), body: var("?body") } }),
        rewrite!("remove-transpose-pair";
            "(app transpose (app transpose ?x))" => "?x"),

        // movement
        rewrite!("map-slide-before-transpose";
            "(app transpose (app (app map (app (app slide ?sz) ?sp)) ?y))" =>
            "(app (app map transpose) (app (app (app slide ?sz) ?sp) (app transpose ?y)))"),
        rewrite!("map-split-before-transpose";
            "(app transpose (app (app map (app split ?n)) ?y))" =>
            "(app (app map transpose) (app (app split ?n) (app transpose ?y)))"),
        rewrite!("slide-before-map-map-f";
            "(app (app map (app map ?f)) (app (app (app slide ?sz) ?sp) ?y))" =>
            "(app (app (app slide ?sz) ?sp) (app (app map ?f) ?y))"),
        rewrite!("split-before-map-map-f";
            "(app (app map (app map ?f)) (app (app split ?n) ?y))" =>
            "(app (app split ?n) (app (app map ?f) ?y))"),
        rewrite!("slide-before-map";
            "(app (app (app slide ?sz) ?sp) (app (app map ?f) ?y))" =>
            "(app (app map (app map ?f)) (app (app (app slide ?sz) ?sp) ?y))"),

        // lowering
        rewrite!("reduce-seq-unroll"; "reduce" => "reduceSeqUnroll"),
        rewrite!("map-seq"; "map" => "mapSeq"),
        rewrite!("iterate-stream"; "map" => "iterateStream"),
        rewrite!("to-mem-after-map-seq";
            "(app (app mapSeq ?f) ?x)" => "(app toMem (app (app mapSeq ?f) ?x))"),
        rewrite!("rotate-values-simplified";
            "(app (app slide ?sz) 1)" => "(app rotateValues ?sz)"),

        // domain-specific
        rewrite!("separate-dot-hv-simplified";
            "(app (app (app reduce add) 0) (app (app map mulT) (app (app zip (app join weights2d)) (app join ?nbh))))" =>
            { with_fresh_var("?sdhv", "(app (app (app reduce add) 0) (app (app map mulT) (app (app zip weightsV) (app (app map (lam ?sdhv (app (app (app reduce add) 0) (app (app map mulT) (app (app zip weightsH) (var ?sdhv)))))) ?nbh))))") }),
        rewrite!("separate-dot-vh-simplified";
            "(app (app (app reduce add) 0) (app (app map mulT) (app (app zip (app join weights2d)) (app join ?nbh))))" =>
            { with_fresh_var("?sdvh", "(app (app (app reduce add) 0) (app (app map mulT) (app (app zip weightsH) (app (app map (lam ?sdvh (app (app (app reduce add) 0) (app (app map mulT) (app (app zip weightsV) (var ?sdvh)))))) (app transpose ?nbh)))))") }),
    ];
    let mut map: HashMap<String, _> = all.into_iter().map(|r| (r.name().to_owned(), r)).collect();
    names.into_iter().map(|&n| map.remove(n).expect("rule not found")).collect()
}

struct BetaApplier {
    v: Var,
    e: Var,
    body: Var,
}

impl Applier<Rise, RiseAnalysis> for BetaApplier {
    fn apply_one(&self, egraph: &mut RiseEGraph, eclass: Id, subst: &Subst) -> Vec<Id> {
        let new_id = substitute_ident(
            egraph, subst[self.v], subst[self.e], subst[self.body]);
        vec![eclass, new_id]
    }
}

// returns a new body where var becomes expr
fn substitute_ident(egraph: &mut RiseEGraph, var: Id, expr: Id, body: Id) -> Id {
    struct Env<'a> {
        egraph: &'a mut RiseEGraph,
        var: Id,
        expr: Id,
        visited: HashMap<Id, Id>
    }

    fn rec_class(eclass: Id, env: &mut Env) -> Id {
        match env.visited.get(&eclass).map(|id| *id) {
            Some(id) => id,
            None =>
                if !env.egraph[eclass].data.free.contains(&env.var) {
                    // println!("avoided");
                    eclass
                } else {
                    let enodes = env.egraph[eclass].nodes.clone();
                    // println!("enodes: {:?}", enodes);
                    // add a dummy node to avoid cycles
                    let dummy = env.egraph.add(Rise::Symbol(format!("_{}_{}_{}", eclass, env.var, env.expr).into()));
                    env.visited.insert(eclass, dummy);
                    let new_ids: Vec<_> = {
                        enodes.into_iter().map(|enode| {
                            match enode {
                                Rise::Var(v) if v == env.var => Ok(env.expr),
                                Rise::Var(_) => Err(enode),
                                Rise::Symbol(_) => Err(enode),
                                Rise::Lambda([v, e]) =>
                                    if env.egraph[env.expr].data.free.contains(&v) {
                                        panic!("TODO: capture avoid")
                                    } else {
                                        Err(Rise::Lambda([v, rec_class(e, env)]))
                                    },
                                Rise::App([f, e]) =>
                                    Err(Rise::App([rec_class(f, env), rec_class(e, env)])),
                                _ => panic!("did not expect {:?}", enode)
                            }
                        }).collect()
                    };
                    let new_ids = new_ids.into_iter().map(|x| {
                        match x {
                            Ok(id) => id,
                            Err(enode) => env.egraph.add(enode),
                        }
                    }).collect::<Vec<_>>().into_iter();
                    let result = new_ids.fold(dummy, |a, b| {
                        // println!("union: {:?} + {:?}", env.egraph[a].nodes, env.egraph[b].nodes);
                        let (id, _) = env.egraph.union(a, b);
                        id
                    });
                    env.visited.insert(eclass, result);
                    result
                }
        }
    }

    let visited = HashMap::new();
    rec_class(body, &mut Env { egraph, var, expr, visited })
}

fn with_fresh_var(name: &str, pattern: &str) -> MakeFresh {
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
    let original_vec = e.as_ref();
    let mut pattern_vec = Vec::new();
    pattern_vec.extend(original_vec.iter().cloned().map(ENodeOrVar::ENode));

    let mut sym_map = HashMap::new();
    fn rec(index: usize, original_vec: &[Rise], pattern_vec: &mut [ENodeOrVar<Rise>], sym_map: &mut HashMap<Symbol, Symbol>) {
        match original_vec[index] {
            Rise::Var(id) => rec(id.into(), original_vec, pattern_vec, sym_map),
            Rise::App([f, e]) => {
                rec(f.into(), original_vec, pattern_vec, sym_map);
                rec(e.into(), original_vec, pattern_vec, sym_map);
            }
            Rise::Lambda([x, e]) => {
                let s = match original_vec[usize::from(x)] {
                    Rise::Symbol(s) => s,
                    _ => panic!("expected symbol for lambda")
                };
                sym_map.insert(s, format!("?{}", s.as_str()).into()).is_none() || panic!("symbol duplicate");
                rec(x.into(), original_vec, pattern_vec, sym_map);
                rec(e.into(), original_vec, pattern_vec, sym_map);
            }
            Rise::Symbol(sym) => {
                use std::str::FromStr;
                pattern_vec[index] = sym_map.get(&sym).cloned().map(|s| ENodeOrVar::Var(Var::from_str(s.as_str()).unwrap()))
                    .unwrap_or(ENodeOrVar::ENode(Rise::Symbol(sym)));
            }
            Rise::Number(_) => ()
        }
    }

    rec(original_vec.len() - 1, original_vec, &mut pattern_vec[..], &mut sym_map);
    println!("{}", e);
    let p: RecExpr<ENodeOrVar<_>> = pattern_vec.into();
    let p = p.into();
    println!("{}", p);
    p
}

fn prove_equiv(name: &str, start_s: String, goal_s: String, rule_names: &[&str]) {
    println!();
    println!("{}", name);

    let start = start_s.parse().unwrap();
    let goal = goal_s.parse().unwrap();
    println!("starting from {}", start);

    let norm_rules = rules(&[
        "eta", "beta"
    ]);
    let runner = Runner::default().with_expr(&goal).run(&norm_rules);
    let (egraph, root) = (runner.egraph, runner.roots[0]);
    egraph.dot().to_svg("/tmp/goal.svg").unwrap();
    struct RiseAstSize; // FIXME: this extracts invalid programs ..
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
        .with_node_limit(10_000)
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
    runner.egraph.dot().to_svg(format!("/tmp/{}.svg", name)).unwrap();
    runner.egraph.check_goals(id, &goals);
}

fn main() {
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

/*
    let tmp = "(app map (app (app slide 3) 1))".then("(app (app slide 3) 1)").then("(app map transpose)");
    let slide2d_3_1 = tmp.as_str();
    let tmp = format!("(lam a (lam b {}))", "(app (app zip (var a)) (var b))".pipe("(app map mulT)").pipe("(app (app reduce add) 0)"));
    let dot = tmp.as_str();
    let tmp = format!("(lam c (lam d {}))", "(app (app zip (var c)) (var d))".pipe("(app map mulT)").pipe("(app (app reduce add) 0)"));
    let dot2 = tmp.as_str();
    let base = /*slide2d_3_1.then(*/format!(
        /*"(app map (app map */"(lam nbh (app (app {} (app join weights2d)) (app join (var nbh))))"/*))"*/, dot)/*)*/;
    let factorised = /*slide2d_3_1.then(*//*format!(
        "(app map (app map {}))", */format!("(app {} weightsH)", dot).then(format!("(app {} weightsV)", dot))
    /*)*//*)*/;
    prove_equiv("base to factorised", base, factorised);
    */
}
