use egg::*;
use std::collections::HashMap;
use crate::analysis::*;

pub fn count_programs_up_to_size<L: Language, A: Analysis<L>>(egraph: &EGraph<L, A>, eclass: Id, limit: u32) -> HashMap<u32, u64> {
  let mut data = HashMap::new();
  one_shot_analysis_semigroup(egraph, CountProgramsUpToSize { limit }, &mut data);
  data.remove(&eclass).unwrap()
}

struct CountProgramsUpToSize { limit: u32 }

impl<L: Language, A: Analysis<L>> CommutativeSemigroupAnalysis<L, A> for CountProgramsUpToSize {
  type Data = HashMap<u32, u64>;

  fn make<'a>(
      &mut self,
      _egraph: &EGraph<L, A>,
      enode: &L,
      analysis_of: &'a impl Fn(Id) -> &'a Self::Data,
  ) -> Self::Data
  where
      Self::Data: 'a,
  {
    let mut counts = HashMap::<u32, u64>::new();
    let children_counts = enode.children().iter().map(|&id| analysis_of(id))
      .collect::<Vec<_>>();

    fn rec(
      limit: u32,
      counts: &mut HashMap::<u32, u64>,
      children_counts: &[&HashMap<u32, u64>], i: usize,
      size: u32, count: u64
    ) {
      if size > limit {
        return;
      }
      match children_counts.get(i) {
        None => {
          let total = counts.get(&size).cloned().unwrap_or(0) + count;
          counts.insert(size, total);
        }
        Some(&child_counts) => {
          for (s, c) in child_counts {
            rec(limit, counts, children_counts, i + 1, size + s, count * c)
          }
        }
      }
    }

    rec(self.limit, &mut counts, &children_counts[..], 0, 1, 1);
    counts
  }

  fn merge(&mut self, a: &mut Self::Data, b: Self::Data) {
    for (size, count) in b {
      let total = a.get(&size).cloned().unwrap_or(0) + count;
      a.insert(size, total);
    }
  }
}