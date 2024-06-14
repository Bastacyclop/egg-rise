use egg::*;
use std::collections::HashMap;
use crate::analysis::*;

pub fn count_programs_up_to_size<L: Language, A: Analysis<L>>(egraph: &EGraph<L, A>, eclass: Id, limit: u32) -> HashMap<u32, u64> {
  let mut data = HashMap::new();
  one_shot_analysis_semigroup(egraph, CountProgramsUpToSize { limit }, &mut data);
  // println!("data: {:?}", data);
  data.remove(&egraph.find(eclass)).unwrap()
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

#[cfg(test)]
mod tests {
  use super::*;

  fn check_result(mut result: HashMap<u32, u64>, slice: &[(u32, u64)]) {
    for &(size, count) in slice {
      assert!(count != 0);
      match result.remove(&size) {
        None => assert!(false),
        Some(count2) => assert_eq!(count, count2)
      }
    }
    assert!(result.is_empty());
  }

  #[test]
  fn tree() {
    let mut egraph = EGraph::<SymbolLang, ()>::new(());
    let a = egraph.add(SymbolLang::leaf("a"));
    let b = egraph.add(SymbolLang::leaf("b"));
    let add = egraph.add(SymbolLang::new("+", vec![a, b]));
    egraph.rebuild();

    let limit = 5;
    let result = count_programs_up_to_size(&egraph, add, limit);
    check_result(result, &[(3, 1)]);
  }

  #[test]
  fn share() {
    let mut egraph = EGraph::<SymbolLang, ()>::new(());
    let a = egraph.add(SymbolLang::leaf("a"));
    let b = egraph.add(SymbolLang::leaf("b"));
    let c = egraph.add(SymbolLang::leaf("c"));
    let d = egraph.add(SymbolLang::leaf("d"));
    let ab = egraph.add(SymbolLang::new("+", vec![a, b]));
    let ba = egraph.add(SymbolLang::new("+", vec![b, a]));
    let cd = egraph.add(SymbolLang::new("+", vec![c, d]));
    let dc = egraph.add(SymbolLang::new("+", vec![d, c]));
    let abcd = egraph.add(SymbolLang::new("+", vec![ab, cd]));
    egraph.union(ab, ba);
    egraph.union(cd, dc);
    egraph.rebuild();

    let limit = 10;
    let result = count_programs_up_to_size(&egraph, abcd, limit);
    println!("{:?}", result);
    check_result(result, &[(7, 4)]);
  }

  #[test]
  fn cycle1() {
    let mut egraph = EGraph::<SymbolLang, ()>::new(());
    let a = egraph.add(SymbolLang::leaf("a"));
    let z = egraph.add(SymbolLang::leaf("0"));
    let add = egraph.add(SymbolLang::new("+", vec![a, z]));
    egraph.union(a, add);
    egraph.rebuild();

    let limit = 8;
    let result = count_programs_up_to_size(&egraph, add, limit);
    check_result(result, &[(1, 1), (3, 1), (5, 1), (7, 1)]);
  }
}