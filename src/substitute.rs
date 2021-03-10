use egg::*;
use crate::rise::*;
use std::collections::HashMap;

pub fn substitute_expr(var: Symbol, expr: &RecExpr<Rise>, body: &RecExpr<Rise>) -> RecExpr<Rise> {
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
pub fn substitute_eclass(egraph: &mut RiseEGraph, var: Id, expr: Id, body: Id) -> Id {
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
                                    let e2 = replace_eclass(env.egraph, v, v2, e);
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
fn replace_eclass(egraph: &mut RiseEGraph, var: Id, new_var: Id, body: Id) -> Id {
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
