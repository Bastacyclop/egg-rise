use egg::*;
use crate::dbrise::*;
use crate::dbsubstitute::*;
use std::collections::HashMap;

fn var(s: &str) -> Var {
    s.parse().unwrap()
}

fn contains_ident(v1: Var, index: Index) -> impl Fn(&mut DBRiseEGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph[subst[v1]].data.free.contains(&index)
}

fn neg(f: impl Fn(&mut DBRiseEGraph, Id, &Subst) -> bool) -> impl Fn(&mut DBRiseEGraph, Id, &Subst) -> bool {
    move |egraph, id, subst| !f(egraph, id, subst)
}

pub fn dbrules(names: &[&str]) -> Vec<Rewrite<DBRise, DBRiseAnalysis>> {
    let all = vec![
        // algorithmic
        rewrite!("map-fusion";
            "(app (app map ?f) (app (app map ?g) ?arg))" =>
            { with_shifted_up(var("?f"), var("?fu"), 0, with_shifted_up(var("?g"), var("?gu"), 0,
                "(app (app map (lam (app ?fu (app ?gu %0)))) ?arg)".parse::<Pattern<DBRise>>().unwrap()
            ))}),
        rewrite!("map-fission";
            "(app map (lam (app ?f ?gx)))" =>
            { with_shifted_up(var("?gx"), var("?gxu"), 1,
                "(lam (app (app map ?f) (app (app map (lam ?gxu)) %0)))".parse::<Pattern<DBRise>>().unwrap()
            )}
            // TODO: if conditions should be recursive filters?
            if neg(contains_ident(var("?f"), Index(0)))),

        // reductions
        rewrite!("eta"; "(lam (app ?f %0))" =>
            { with_shifted_down(var("?f"), var("?fd"), 1, "?fd".parse::<Pattern<DBRise>>().unwrap()) }
            // TODO: if conditions should be recursive filters?
            if neg(contains_ident(var("?f"), Index(0)))),
        rewrite!("beta"; "(app (lam ?body) ?e)" =>
            { BetaExtractApplier { body: var("?body"), subs: var("?e") } }),
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

        // mulT = (lam (app (app mul (app fst %0)) (app snd %0)))
        rewrite!("separate-dot-hv-simplified";
            "(app (app (app reduce add) 0) (app (app map (lam (app (app mul (app fst %0)) (app snd %0)))) (app (app zip (app join weights2d)) (app join ?nbh))))" =>
            "(app (app (app reduce add) 0) (app (app map (lam (app (app mul (app fst %0)) (app snd %0)))) (app (app zip weightsV) (app (app map (lam (app (app (app reduce add) 0) (app (app map (lam (app (app mul (app fst %0)) (app snd %0)))) (app (app zip weightsH) %0))))) ?nbh))))"),
        rewrite!("separate-dot-vh-simplified";
            "(app (app (app reduce add) 0) (app (app map (lam (app (app mul (app fst %0)) (app snd %0)))) (app (app zip (app join weights2d)) (app join ?nbh))))" =>
            "(app (app (app reduce add) 0) (app (app map (lam (app (app mul (app fst %0)) (app snd %0)))) (app (app zip weightsH) (app (app map (lam (app (app (app reduce add) 0) (app (app map (lam (app (app mul (app fst %0)) (app snd %0)))) (app (app zip weightsV) %0))))) (app transpose ?nbh)))))"),
    ];
    let mut map: HashMap<String, _> = all.into_iter().map(|r| (r.name().to_owned(), r)).collect();
    names.into_iter().map(|&n| map.remove(n).expect("rule not found")).collect()
}

struct BetaExtractApplier {
    body: Var,
    subs: Var,
}

impl Applier<DBRise, DBRiseAnalysis> for BetaExtractApplier {
    fn apply_one(&self, egraph: &mut DBRiseEGraph, _eclass: Id, subst: &Subst) -> Vec<Id> {
        let ex_body = &egraph[subst[self.body]].data.beta_extract;
        let ex_subs = &egraph[subst[self.subs]].data.beta_extract;
        let result = beta_reduce(ex_body, ex_subs);
        vec![egraph.add_expr(&result)]
    }
}

fn with_shifted_up<A>(var: Var, new_var: Var, cutoff: u32, applier: A) -> Shifted<A>
    where A: Applier<DBRise, DBRiseAnalysis> {
    Shifted {
        var,
        new_var,
        up: true,
        cutoff: Index(cutoff),
        applier
    }
}

fn with_shifted_down<A>(var: Var, new_var: Var, cutoff: u32, applier: A) -> Shifted<A>
    where A: Applier<DBRise, DBRiseAnalysis> {
    Shifted {
        var,
        new_var,
        up: false,
        cutoff: Index(cutoff),
        applier
    }
}

struct Shifted<A> {
    var: Var,
    new_var: Var,
    up: bool,
    cutoff: Index,
    applier: A,
}

impl<A> Applier<DBRise, DBRiseAnalysis> for Shifted<A> where A: Applier<DBRise, DBRiseAnalysis> {
    fn apply_one(&self, egraph: &mut DBRiseEGraph, eclass: Id, subst: &Subst) -> Vec<Id> {
        let extract = &egraph[subst[self.var]].data.beta_extract;
        let shifted = shift_copy(extract, self.up, self.cutoff);
        let mut subst = subst.clone();
        subst.insert(self.new_var, egraph.add_expr(&shifted));
        self.applier.apply_one(egraph, eclass, &subst)
    }
}