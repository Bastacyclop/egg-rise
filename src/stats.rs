use crate::*;
use memory_stats::memory_stats;

const ITER_LIMIT: usize = 20;
const NODE_LIMIT: usize = 1_000_000;
const MEMORY_LIMIT: usize = 4_000_000_000;
const TIME_LIMIT: std::time::Duration = std::time::Duration::from_secs(4 * 60); // 4mn

pub fn grow_egraph_until<L, A, S>(
  search_name: &str,
  egraph: EGraph<L, A>,
  rules: &[Rewrite<L, A>],
  root: Id,
  size_limit: u32,
  mut satisfied: S
) -> EGraph<L, A>
where S: FnMut(&mut Runner<L, A>) -> bool + 'static,
      L: Language, A: Analysis<L>, A: Default
{
  let search_name_hook = search_name.to_owned();
  let runner = egg::Runner::default()
      .with_scheduler(egg::SimpleScheduler)
      .with_iter_limit(ITER_LIMIT)
      .with_node_limit(NODE_LIMIT)
      .with_time_limit(TIME_LIMIT)
      .with_hook(move |runner| {
        let mut out_of_memory = false;
        // hook 0 <- nothing
        // iteration 0
        // hook 1 <- #0 size etc after iteration 0 + memory after iteration 0
        if let Some(it) = runner.iterations.last() {
          out_of_memory = iteration_stats(&search_name_hook, &runner.egraph, it, runner.iterations.len(), root, size_limit);
        }

        if satisfied(runner) {
          Err(String::from("Satisfied"))
        } else if out_of_memory {
          Err(String::from("Out of Memory"))
        } else {
          Ok(())
        }
      })
      .with_egraph(egraph)
      .run(&rules[..]);
  iteration_stats(search_name, &runner.egraph, runner.iterations.last().unwrap(), runner.iterations.len(), root, size_limit);
  runner.print_report();
  /*
    let rules = runner.iterations.iter().map(|i|
        i.applied.iter().map(|(_, n)| n).sum::<usize>()).sum::<usize>();
    println!("applied rules: {}", rules);
    runner.iterations.iter().for_each(|i| println!("{:?}", i));
    runner.egraph.dot().to_svg(format!("/tmp/{}.svg", name)).unwrap();
  */
  runner.egraph
}

// search name,
// iteration number,
// physical memory,
// virtual memory,
// e-graph nodes,
// e-graph classes,
// amount of terms represented with size < size_limit,
// applied rules,
// total time,
// hook time,
// search time,
// apply time,
// rebuild time
pub fn iteration_stats<L: Language, A: Analysis<L>>(
  search_name: &str,
  egraph: &EGraph<L, A>,
  it: &egg::Iteration<()>,
  it_number: usize,
  root: Id,
  size_limit: u32,
) -> bool {
  let memory = memory_stats().expect("could not get current memory usage");
  let out_of_memory = memory.virtual_mem > MEMORY_LIMIT;
  let found = match &it.stop_reason {
      Some(egg::StopReason::Other(s)) => s == "Satisfied",
      _ => false,
  };
  eprintln!("{}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}",
      search_name,
      it_number,
      memory.physical_mem,
      memory.virtual_mem,
      it.egraph_nodes,
      it.egraph_classes,
      count::sum_programs_up_to_size(&count::count_programs_up_to_size(egraph, root, size_limit)),
  // count_alpha_equiv(&mut runner.egraph),
      it.applied.iter().map(|(_, &n)| n).sum::<usize>(),
      it.total_time,
      it.hook_time,
      it.search_time,
      it.apply_time,
      it.rebuild_time,
      found);
  out_of_memory
}