use egg::*;
use std::collections::{HashSet, HashMap};

define_language! {
    enum Rise {
        "var" = Var(Id),
        "app" = App([Id; 2]),
        "lam" = Lambda([Id; 2]),

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

fn rules() -> Vec<Rewrite<Rise, RiseAnalysis>> {
    vec![
        rewrite!("map-fusion";
                 "(app (app map ?f) (app (app map ?g) ?arg))" =>
                 { with_fresh_var("?mfu", "(app (app map (lam ?mfu (app ?f (app ?g (var ?mfu))))) ?arg)") }),
        rewrite!("map-fission";
                 "(app map (lam ?x (app ?f ?gx)))" =>
                 { with_fresh_var("?mfi", "(lam ?mfi (app (app map ?f) (app (app map (lam ?x ?gx)) (var ?mfi))))") }
                 if neg(contains_ident(var("?f"), var("?x")))),

        rewrite!("eta"; "(lam ?v (app ?f (var ?v)))" => "?f"
            if neg(contains_ident(var("?f"), var("?v")))),
        rewrite!("beta"; "(app (lam ?v ?body) ?e)" =>
                 { BetaApplier { v: var("?v"), e: var("?e"), body: var("?body") } })
    ]
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
                    eclass
                } else {
                    let enodes = env.egraph[eclass].nodes.clone();
                    let new_ids: Vec<_> = {
                        enodes.into_iter().map(|enode| {
                            match enode {
                                Rise::Var(v) if v == env.var => Ok(env.expr),
                                Rise::Var(_) => Ok(eclass),
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
                    let mut new_ids = new_ids.into_iter().map(|x| {
                        match x {
                            Ok(id) => id,
                            Err(enode) => env.egraph.add(enode),
                        }
                    }).collect::<Vec<_>>().into_iter();
                    let first_id = new_ids.next().expect("no new ids");
                    new_ids.fold(first_id, |a, b| {
                        let (id, _) = env.egraph.union(a, b);
                        id
                    })
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

trait DSL {
    // f1 >> f2
    fn then<S: Into<String>>(self, other: S) -> String;
    // using patterns for alpha-equivalence
    fn then_p<S: Into<String>>(self, other: S) -> String;
}

static mut COUNTER: u32 = 0;
fn fresh_id() -> u32 {
    unsafe {
        let c = COUNTER;
        COUNTER += 1;
        c
    }
}

impl DSL for String {
    fn then<S: Into<String>>(self, other: S) -> String {
        let c = fresh_id();
        format!("(lam x{} (app {} (app {} (var x{}))))", c, other.into(), self, c)
    }

    fn then_p<S: Into<String>>(self, other: S) -> String {
        let c = fresh_id();
        format!("(lam ?x{} (app {} (app {} (var ?x{}))))", c, other.into(), self, c)
    }
}

impl DSL for &str {
    fn then<S: Into<String>>(self, other: S) -> String {
        String::from(self).then(other)
    }
    fn then_p<S: Into<String>>(self, other: S) -> String {
        String::from(self).then_p(other)
    }
}

fn prove_equiv(name: &str, start_s: String, goal_s: String) {
    println!();
    println!("{}", name);

    let start = start_s.parse().unwrap();
    let goal = goal_s.parse().unwrap();
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
        "(app map (app (app padClamp 1) 1))".then_p(
        "(app (app padClamp 1) 1)".then_p(
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
        format!("(app map {})", "(var f1)".then_p("(var f2)")).then_p(format!("(app map {})", "(var f3)".then_p("(var f4)")))
    );

    prove_equiv("simple map fission",
        format!("(app map {})", "(var f1)".then("(var f2)").then("(var f3)").then("(var f4)")),
        "(app map (var f1))".then_p("(app map (var f2))").then_p("(app map (var f3))").then_p("(app map (var f4))")
    );

    prove_equiv("map fusion + map fission",
        format!("(app map {})", "(var f1)".then("(var f2)").then("(var f3)").then("(var f4)")),
        format!("(app map {})", "(var f1)".then_p("(var f2)")).then_p(format!("(app map {})", "(var f3)".then_p("(var f4)")))
    );
}
