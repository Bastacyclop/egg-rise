use egg::*;
use std::collections::{HashSet, HashMap};
use std::cmp::Ordering;

define_language! {
    enum Rise {
        "var" = Var(Id),
        "app" = App([Id; 2]),
        "lam" = Lambda([Id; 2]),

        ">>" = Then([Id; 2]),

        Number(i32),
        Symbol(Symbol),
    }
}

type RiseEGraph = EGraph<Rise, RiseAnalysis>;

#[derive(Default)]
struct RiseAnalysis;

#[derive(Default, Debug)]
struct Data {
    free: HashSet<Id>,
    beta_extract: RecExpr<Rise>,
}

impl Analysis<Rise> for RiseAnalysis {
    type Data = Data;

    fn merge(&self, to: &mut Data, from: Data) -> Option<Ordering> {
        let before_len = to.free.len();
        to.free.extend(from.free);
        let mut did_change = before_len != to.free.len();
        if !from.beta_extract.as_ref().is_empty() &&
            (to.beta_extract.as_ref().is_empty() ||
                to.beta_extract.as_ref().len() > from.beta_extract.as_ref().len()) {
            to.beta_extract = from.beta_extract;
            did_change = true;
        }
        if did_change { None } else { Some(Ordering::Greater) }
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
        let beta_extract = enode.to_recexpr(|id| egraph[id].data.beta_extract.as_ref());
        Data { free, beta_extract }
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
        // TODO: if conditions should be recursive filters?

        rewrite!("map-fusion-then";
            "(>> (app map ?f) (app map ?g))" => "(app map (>> ?f ?g))"),
        rewrite!("map-fission-then";
            "(app map (>> ?f ?g))" => "(>> (app map ?f) (app map ?g))"),
        rewrite!("then-assoc-1"; "(>> ?f (>> ?g ?h))" => "(>> (>> ?f ?g) ?h)"),
        rewrite!("then-assoc-2"; "(>> (>> ?f ?g) ?h)" => "(>> ?f (>> ?g ?h))"),

        // reductions
        rewrite!("eta"; "(lam ?v (app ?f (var ?v)))" => "?f"
            if neg(contains_ident(var("?f"), var("?v")))),
        rewrite!("beta"; "(app (lam ?v ?body) ?e)" =>
            //{ BetaApplier { v: var("?v"), e: var("?e"), body: var("?body") } }),
            { BetaExtractApplier { v: var("?v"), e: var("?e"), body: var("?body") } }),
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
    fn apply_one(&self, egraph: &mut RiseEGraph, _eclass: Id, subst: &Subst) -> Vec<Id> {
        let new_id = substitute_ident(
            egraph, subst[self.v], subst[self.e], subst[self.body]);
        vec![new_id]
    }
}

struct BetaExtractApplier {
    v: Var,
    e: Var,
    body: Var,
}

impl Applier<Rise, RiseAnalysis> for BetaExtractApplier {
    fn apply_one(&self, egraph: &mut RiseEGraph, _eclass: Id, subst: &Subst) -> Vec<Id> {
        let ex_body = &egraph[subst[self.body]].data.beta_extract;
        let ex_e = &egraph[subst[self.e]].data.beta_extract;
        let v_sym = {
            let ns = &egraph[subst[self.v]].nodes;
            assert!(ns.len() == 1);
            match &ns[0] {
                &Rise::Symbol(sym) => sym,
                n => panic!("expected symbol, found {:?}", n)
            }
        };
        // println!("before subs: {} [{} / {}]", ex_body, ex_e, v_sym);
        let result = substitute_expr(v_sym, ex_e, ex_body);
        // println!("after subs:  {}", result);
        vec![egraph.add_expr(&result)]
    }
}

fn substitute_expr(var: Symbol, expr: &RecExpr<Rise>, body: &RecExpr<Rise>) -> RecExpr<Rise> {
    struct Env<'a> {
        var: Symbol,
        expr: &'a RecExpr<Rise>,
        body: &'a [Rise],
        result: &'a mut RecExpr<Rise>
    }

    fn add_expr(to: &mut RecExpr<Rise>, e: &[Rise], id: Id) -> Id {
        let node = e[usize::from(id)].clone().map_children(|id| add_expr(to, e, id));
        to.add(node)
    }

    fn expr_contains(e: &[Rise], var: Symbol) -> bool {
        for node in e {
            if node == &Rise::Symbol(var) {
                return true
            }
        }
        false
    }

    fn find_fresh_symbol(a: &[Rise], b: &[Rise]) -> Symbol {
        for i in 0..std::usize::MAX {
            let s = Symbol::from(format!("s{}", i));
            if !expr_contains(a, s) && !expr_contains(b, s) {
                return s;
            }
        }
        panic!("could not find fresh symbol")
    }

    fn replace_expr(e: &[Rise], id: Id, v: Symbol, v2: Symbol) -> RecExpr<Rise> {
        fn replace_add(to: &mut RecExpr<Rise>, e: &[Rise], id: Id, v: Symbol, v2: Symbol) -> Id {
            let node = e[usize::from(id)].clone();
            let result = match node {
                Rise::Symbol(v) => Rise::Symbol(v2),
                _ => node.map_children(|id| replace_add(to, e, id, v, v2))
            };
            to.add(result)
        }
        let mut result = RecExpr::default();
        replace_add(&mut result, e, id, v, v2);
        result
    }

    fn unwrap_symbol(n: &Rise) -> Symbol {
        match n {
            &Rise::Symbol(s) => s,
            _ => panic!("expected symbol")
        }
    }

    fn rec(index: usize, env: &mut Env) -> Id {
        match &env.body[index] {
            &Rise::Var(v) if env.body[usize::from(v)] == Rise::Symbol(env.var) =>
                add_expr(env.result, env.expr.as_ref(), Id::from(env.expr.as_ref().len() - 1)),
            Rise::Var(_) | Rise::Symbol(_) | Rise::Number(_) =>
                add_expr(env.result, env.body, Id::from(index)),
            &Rise::Lambda([v, _]) if env.body[usize::from(v)] == Rise::Symbol(env.var) =>
                add_expr(env.result, env.body, Id::from(index)),
            &Rise::Lambda([v, e])
            if expr_contains(env.expr.as_ref(),
                             unwrap_symbol(&env.body[usize::from(v)])) =>
            {
                let v2 = find_fresh_symbol(env.body, env.expr.as_ref());
                let e2 = replace_expr(env.body, e,
                                      unwrap_symbol(&env.body[usize::from(v)]), v2);
                let mut e3 = substitute_expr(env.var, env.expr, &e2);
                let ide3 = Id::from(e3.as_ref().len() - 1);
                let v2e3 = e3.add(Rise::Symbol(v2));
                e3.add(Rise::Lambda([v2e3, ide3]));
                add_expr(env.result, e3.as_ref(), Id::from(e3.as_ref().len() - 1))
            }
            &Rise::Lambda([v, e]) => {
                let v2 = rec(usize::from(v), env);
                let e2 = rec(usize::from(e), env);
                env.result.add(Rise::Lambda([v, e2]))
            }
            &Rise::App([f, e]) => {
                let f2 = rec(usize::from(f), env);
                let e2 = rec(usize::from(e), env);
                env.result.add(Rise::App([f2, e2]))
            }
            node => panic!("did not expect {:?}", node)
        }
    }

    let mut result = RecExpr::default();
    rec(body.as_ref().len() - 1, &mut Env {
        var,
        expr,
        body: body.as_ref(),
        result: &mut result
    });
    result
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
                    eclass
                } else {
                    let enodes = env.egraph[eclass].nodes.clone();
                    // add a dummy node to avoid cycles
                    let dummy = env.egraph.reserve();
                    // env.egraph.add(Rise::Symbol(format!("_s_{}_{}_{}", eclass, env.var, env.expr).into()));
                    env.visited.insert(eclass, dummy);
                    let final_id = enodes.into_iter().fold(dummy, |current_id, enode| {
                        let new_id = match enode {
                            Rise::Var(v) if env.egraph.find(v) == env.egraph.find(env.var) => env.expr,
                            // ignore dummies
                            // Rise::Symbol(s) if s.as_str().starts_with("_") => dummy,
                            Rise::Var(_) | Rise::Symbol(_) => {
                                panic!("{:?}", enode);
                                // keeping same e-node would merge the new class with previous class
                            }
                            Rise::Lambda([v, e]) =>
                                if env.egraph.find(v) == env.egraph.find(env.var) {
                                    panic!("{:?}", v)
                                    // keeping same e-node would merge the new class with previous class
                                } else if env.egraph[env.expr].data.free.contains(&v) {
                                    env.egraph.rebuild();
                                    env.egraph.dot().to_svg("/tmp/cap-avoid.svg").unwrap();
                                    panic!("FIXME: capture avoid {:?} {:?}", env.egraph[v], env.egraph[env.var]);
                                    let v2 = env.egraph.add(
                                        Rise::Symbol(format!("subs_{}_{}_{}", eclass, env.var, env.expr).into()));
                                    println!("capture avoid {}, {}, {}, {}, {}, {}", eclass, v2, v, e, env.var, env.expr);
                                    let e2 = replace_ident(env.egraph, v, v2, e);
                                    let r = Rise::Lambda([v2, rec_class(e2, env)]);
                                    env.egraph.add(r)
                                } else {
                                    let r = Rise::Lambda([v, rec_class(e, env)]);
                                    env.egraph.add(r)
                                },
                            Rise::App([f, e]) => {
                                let r = Rise::App([rec_class(f, env), rec_class(e, env)]);
                                env.egraph.add(r)
                            }
                            _ => panic!("did not expect {:?}", enode)
                        };
                        let (new_id, _) = env.egraph.union(current_id, new_id);
                        new_id
                    });
                    env.visited.insert(eclass, final_id);
                    final_id
                }
        }
    }

    let visited = HashMap::new();
    // egraph.rebuild();
    // egraph.dot().to_svg(format!("/tmp/before_{}_{}_{}.svg", var, expr, body)).unwrap();
    let r = rec_class(body, &mut Env { egraph, var, expr, visited });
    // egraph.rebuild();
    // egraph.dot().to_svg(format!("/tmp/after_{}_{}_{}.svg", var, expr, body)).unwrap();
    r
}

// returns a new body where var is replaced by expr
fn replace_ident(egraph: &mut RiseEGraph, var: Id, new_var: Id, body: Id) -> Id {
    struct Env<'a> {
        egraph: &'a mut RiseEGraph,
        var: Id,
        new_var: Id,
        visited: HashMap<Id, Id>
    }

    fn rec_class(eclass: Id, env: &mut Env) -> Id {
        match env.visited.get(&eclass).map(|id| *id) {
            Some(id) => id,
            None =>
                if eclass == env.var {
                    env.new_var
                } else {
                    let enodes = env.egraph[eclass].nodes.clone();
                    // add a dummy node to avoid cycles
                    let dummy = env.egraph.add(Rise::Symbol(format!("_r_{}_{}_{}", eclass, env.var, env.new_var).into()));
                    env.visited.insert(eclass, dummy);
                    let final_id =
                        enodes.into_iter().fold(dummy, |current_id, enode| {
                            let new_enode = enode.map_children(|c| rec_class(c, env));
                            let new_id = env.egraph.add(new_enode);
                            let (new_id, _) = env.egraph.union(current_id, new_id);
                            new_id
                        });
                    env.visited.insert(eclass, final_id);
                    final_id
                }
        }
    }

    let visited = HashMap::new();
    rec_class(body, &mut Env { egraph, var, new_var, visited })
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
        "eta", "beta"
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
        .with_node_limit(40_000)
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

    let scanline_half = "(app (app slide 3) 1)".then(format!(
        "(app map {})",
            "transpose".then(
            "(app (app slide 3) 1)").then(format!(
            "(app map {})",
                "transpose".then("transpose").then(
                format!("(app map (app {} weightsV))", dot)).then(
                format!("(app {} weightsH)", dot2))))
    ));

    // FIXME: equivalence not proven when adding unused map fission rule
    prove_equiv("base to scanline half", base.clone(), scanline_half, &[
        /*"eta", */"beta", "remove-transpose-pair", "map-fusion", "map-fission",
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    // beta impl issue?

    // FIXME:
    prove_equiv("base to scanline", base, scanline, &[
        "eta", "beta", "remove-transpose-pair", "map-fusion", "map-fission",
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
}
