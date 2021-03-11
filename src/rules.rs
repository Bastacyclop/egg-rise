use egg::*;
use crate::rise::*;
use crate::substitute::*;
use std::collections::HashMap;

fn var(s: &str) -> Var {
    s.parse().unwrap()
}

fn contains_ident(v1: Var, v2: Var) -> impl Fn(&mut RiseEGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph[subst[v1]].data.free.contains(&subst[v2])
}

fn neg(f: impl Fn(&mut RiseEGraph, Id, &Subst) -> bool) -> impl Fn(&mut RiseEGraph, Id, &Subst) -> bool {
    move |egraph, id, subst| !f(egraph, id, subst)
}

pub fn rules(names: &[&str]) -> Vec<Rewrite<Rise, RiseAnalysis>> {
    let all = vec![
        // algorithmic
        rewrite!("map-fusion";
            "(app (app map ?f) (app (app map ?g) ?arg))" =>
            { with_fresh_var("?mfu", "(app (app map (lam ?mfu (app ?f (app ?g (var ?mfu))))) ?arg)") }),
        rewrite!("map-fission";
            "(app map (lam ?x (app ?f ?gx)))" =>
            { with_fresh_var("?mfi", "(lam ?mfi (app (app map ?f) (app (app map (lam ?x ?gx)) (var ?mfi))))") }
            // TODO: if conditions should be recursive filters?
            if neg(contains_ident(var("?f"), var("?x")))),

        rewrite!("map-fusion-then";
            "(>> (app map ?f) (app map ?g))" => "(app map (>> ?f ?g))"),
        rewrite!("map-fission-then";
            "(app map (>> ?f ?g))" => "(>> (app map ?f) (app map ?g))"),
        rewrite!("then-assoc-1"; "(>> ?f (>> ?g ?h))" => "(>> (>> ?f ?g) ?h)"),
        rewrite!("then-assoc-2"; "(>> (>> ?f ?g) ?h)" => "(>> ?f (>> ?g ?h))"),

        // reductions
        rewrite!("eta"; "(lam ?v (app ?f (var ?v)))" => "?f"
            // TODO: if conditions should be recursive filters?
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
        let new_id = substitute_eclass(
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
            if ns.len() != 1 {
                panic!("expected symbol, found {:?}", ns);
            }
            match &ns[0] {
                &Rise::Symbol(sym) => sym,
                n => panic!("expected symbol, found {:?}", n)
            }
        };
        let result = substitute_expr(v_sym, ex_e, ex_body);
        vec![egraph.add_expr(&result)]
    }
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