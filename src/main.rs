use egg::*;
use std::collections::{HashSet, HashMap};

define_language! {
    pub enum Rise {
        "var" = Var(Id),
        "app" = App([Id; 2]),
        "lam" = Lambda([Id; 2]),
        "let" = Let([Id; 3]),

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

fn rules(names: &[&str]) -> Vec<Rewrite<Rise, RiseAnalysis>> {
    let all = vec![
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
        rewrite!("let-transpose"; "(let ?v ?e transpose)" => "transpose"),
        rewrite!("let-slide"; "(let ?v ?e slide)" => "slide"),
        rewrite!("let-reduce"; "(let ?v ?e reduce)" => "reduce"),
        rewrite!("let-mulT"; "(let ?v ?e mulT)" => "mulT"),
        rewrite!("let-weights2d"; "(let ?v ?e weights2d)" => "weights2d"),
        rewrite!("let-weightsV"; "(let ?v ?e weightsV)" => "weightsV"),
        rewrite!("let-weightsH"; "(let ?v ?e weightsH)" => "weightsH"),
        rewrite!("let-join"; "(let ?v ?e join)" => "join"),
        rewrite!("let-zip"; "(let ?v ?e zip)" => "zip"),
        rewrite!("let-add"; "(let ?v ?e add)" => "add"),
        rewrite!("let-0"; "(let ?v ?e 0)" => "0"),
        rewrite!("let-1"; "(let ?v ?e 1)" => "1"),
        rewrite!("let-3"; "(let ?v ?e 3)" => "3"),

        rewrite!("remove-transpose-pair";
            "(app transpose (app transpose ?x))" => "?x"),

        // movement
        rewrite!("map-slide-before-transpose";
            "(app transpose (app (app map (app (app slide ?sz) ?sp)) ?y))" =>
            "(app (app map transpose) (app (app (app slide ?sz) ?sp) (app transpose ?y)))"),
        /*
        rewrite!("map-split-before-transpose";
            "(app transpose (app (app map (app split ?n)) ?y))" =>
            "(app (app map transpose) (app (app split ?n) (app transpose ?y)))"),
            */
        rewrite!("slide-before-map-map-f";
            "(app (app map (app map ?f)) (app (app (app slide ?sz) ?sp) ?y))" =>
            "(app (app (app slide ?sz) ?sp) (app (app map ?f) ?y))"),
            /*
        rewrite!("split-before-map-map-f";
            "(app (app map (app map ?f)) (app (app split ?n) ?y))" =>
            "(app (app split ?n) (app (app map ?f) ?y))"),
            */
        rewrite!("slide-before-map";
            "(app (app (app slide ?sz) ?sp) (app (app map ?f) ?y))" =>
            "(app (app map (app map ?f)) (app (app (app slide ?sz) ?sp) ?y))"),

        // lowering
        /*
        rewrite!("reduce-seq-unroll"; "reduce" => "reduceSeqUnroll"),
        rewrite!("map-seq"; "map" => "mapSeq"),
        rewrite!("iterate-stream"; "map" => "iterateStream"),
        rewrite!("to-mem-after-map-seq";
            "(app (app mapSeq ?f) ?x)" => "(app toMem (app (app mapSeq ?f) ?x))"),
        rewrite!("rotate-values-simplified";
            "(app (app slide ?sz) 1)" => "(app rotateValues ?sz)"),
        */
        // domain-specific
        rewrite!("separate-dot-hv-simplified";
            "(app (app (app reduce add) 0) (app (app map mulT) (app (app zip (app join weights2d)) (app join ?nbh))))" =>
            { withFreshVar("?sdhv", "(app (app (app reduce add) 0) (app (app map mulT) (app (app zip weightsV) (app (app map (lam ?sdhv (app (app (app reduce add) 0) (app (app map mulT) (app (app zip weightsH) (var ?sdhv)))))) ?nbh))))") }),
        rewrite!("separate-dot-vh-simplified";
            "(app (app (app reduce add) 0) (app (app map mulT) (app (app zip (app join weights2d)) (app join ?nbh))))" =>
            { withFreshVar("?sdvh", "(app (app (app reduce add) 0) (app (app map mulT) (app (app zip weightsH) (app (app map (lam ?sdvh (app (app (app reduce add) 0) (app (app map mulT) (app (app zip weightsV) (var ?sdvh)))))) (app transpose ?nbh)))))") }),

    ];
    let mut map: HashMap<String, _> = all.into_iter().map(|r| (r.name().to_owned(), r)).collect();
    names.into_iter().map(|&n| map.remove(n).expect(&format!("rule not found: {}", n))).collect()
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


pub fn expr_to_alpha_equiv_pattern(e: RecExpr<Rise>) -> Pattern<Rise> {
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

pub fn expr_fresh_alpha_rename(e: RecExpr<Rise>) -> RecExpr<Rise> {
    expr_alpha_rename(e, |r| r,
                      |s| {
                          let s2 = format!("x{}", freshId());
                          Rise::Symbol(s2.into())
                      },
                      |s| Rise::Symbol(s))
}

pub fn expr_alpha_rename<L, BS, FS>(
    e: RecExpr<Rise>,
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
    }
    fn rec<L, BS, FS>(index: usize, env: &mut Env<L, BS, FS>)
        where L: Language, BS: Fn(Symbol) -> L, FS: Fn(Symbol) -> L
    {
        match env.original_vec[index] {
            Rise::Var(id) => rec(id.into(), env),
            Rise::App([f, e]) => {
                rec(f.into(), env);
                rec(e.into(), env);
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
            Rise::Number(_) => (),
            Rise::Let(_) => panic!("let")
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

trait DSL {
    // f1 >> f2
    fn then<S: Into<String>>(self, other: S) -> String;
    // v |> f
    fn pipe<S: Into<String>>(self, other: S) -> String;
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

pub struct AstSizeNoLet;
impl CostFunction<Rise> for AstSizeNoLet {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &Rise, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let weight = match enode {
            Rise::Let(_) => 1000,
            _ => 1,
        };
        enode.fold(weight, |sum, id| sum + costs(id))
    }
}

fn normalize(e: &RecExpr<Rise>) -> RecExpr<Rise> {
    let norm_rules = rules(&[
        "eta", "beta",
        "let-app", "let-var-same", "let-var-diff", "let-lam-same", "let-lam-diff",
        "let-map", "let-transpose", "let-slide", "let-reduce", "let-mulT",
        "let-weights2d", "let-weightsV", "let-weightsH", "let-join", "let-zip",
        "let-add", "let-0", "let-1", "let-3"
    ]);
    let runner = Runner::default().with_expr(e).run(&norm_rules);
    runner.print_report();
    let (egraph, root) = (runner.egraph, runner.roots[0]);
    let mut extractor = Extractor::new(&egraph, AstSizeNoLet);
    let (_, normalized) = extractor.find_best(root);
    normalized
}

fn prove_equiv(name: &str, startS: String, goalS: String, rule_names: &[&str]) {
    println!();
    println!("{}", name);

    let start = normalize(&startS.parse().unwrap());
    let goal = normalize(&goalS.parse().unwrap());
    println!("starting from {}", start);
    println!("aiming for {}", goal);

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
        .with_node_limit(1_000_000)
        .with_iter_limit(60)
        .with_time_limit(std::time::Duration::from_secs(600))
        .with_hook(move |r| {
            if goals2.iter().all(|g| g.search_eclass(&r.egraph, id).is_some()) {
                Err("Done".into())
            } else {
                Ok(())
            }
        }).run(&rules_to_goal);
    runner.print_report();
    runner.egraph.check_goals(id, &goals);
}

fn main() {
    /*
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
*/
    let tmp = "(app map (app (app slide 3) 1))".then("(app (app slide 3) 1)").then("(app map transpose)");
    let slide2d_3_1 = tmp.as_str();
    let tmp = format!("(lam a (lam b {}))", "(app (app zip (var a)) (var b))".pipe("(app map mulT)").pipe("(app (app reduce add) 0)"));
    let dot = tmp.as_str();
    let tmp = format!("(lam c (lam d {}))", "(app (app zip (var c)) (var d))".pipe("(app map mulT)").pipe("(app (app reduce add) 0)"));
    let dot2 = tmp.as_str();

    let base = slide2d_3_1.then(format!(
        "(app map (app map (lam nbh (app (app {} (app join weights2d)) (app join (var nbh))))))", dot));
    let factorised = slide2d_3_1.then(format!(
        "(app map (app map {}))", format!("(app map (app {} weightsH))", dot).then(format!("(app {} weightsV)", dot2))
    ));
    let factorised2 = slide2d_3_1.then(format!(
        "(app map (app map {}))", "transpose".then(format!("(app map (app {} weightsV))", dot)).then(format!("(app {} weightsH)", dot2))
    ));
    let scanline = "(app (app slide 3) 1)".then(format!(
        "(app map {})",
            "transpose".then(
            format!("(app map (app {} weightsV))", dot)).then(
            "(app (app slide 3) 1)").then(
            format!("(app map (app {} weightsH))", dot2))
    ));
/*
    prove_equiv("base to factorised", base.clone(), factorised,
                &["eta", "beta", "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    prove_equiv("base to factorised2", base.clone(), factorised2,
                &["eta", "beta", "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    let scanline_half_0 = "(app (app slide 3) 1)".then(format!(
        "(app map {})",
            "transpose".then(
            "(app (app slide 3) 1)").then(
            "(app map transpose)").then(format!(
                "(app map {})",
                    "transpose".then(
                    format!("(app map (app {} weightsV))", dot)).then(
                    format!("(app {} weightsH)", dot2))))
    ));
    prove_equiv("base to scanline half 0", base.clone(), scanline_half_0.clone(), &[
        "eta", "beta", "remove-transpose-pair", "map-fusion", "map-fission",
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    let scanline_half = "(app (app slide 3) 1)".then(format!(
        "(app map {})",
            "transpose".then(
            "(app (app slide 3) 1)").then(format!(
            "(app map {})",
                "transpose".then("transpose").then(
                format!("(app map (app {} weightsV))", dot)).then(
                format!("(app {} weightsH)", dot2))))
    ));
    prove_equiv("h0 to h", scanline_half_0, scanline_half.clone(), &[
        "beta", "remove-transpose-pair", "map-fusion", // "map-fission", "eta"
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
    //FIXME:
    prove_equiv("base to scanline half", base.clone(), scanline_half, &[
        "eta", "beta", "remove-transpose-pair", "map-fusion", "map-fission",
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
*/
    // FIXME:
    prove_equiv("base to scanline", base, scanline, &[
        "eta", "beta",
        "let-app", "let-var-same", "let-var-diff", "let-lam-same", "let-lam-diff",
        "let-map", "let-transpose", "let-slide", "let-reduce", "let-mulT",
        "let-weights2d", "let-weightsV", "let-weightsH", "let-join", "let-zip",
        "let-add", "let-0", "let-1", "let-3",
        "remove-transpose-pair", "map-fusion", "map-fission",
        "slide-before-map", "map-slide-before-transpose", "slide-before-map-map-f",
        "separate-dot-vh-simplified", "separate-dot-hv-simplified"]);
}
