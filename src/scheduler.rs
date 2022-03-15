use egg::*;
use std::collections::HashMap;

pub struct Scheduler {
    match_limit: usize,
    ban_length: usize,
    stats: HashMap<String, RuleStats>,
}

struct RuleStats {
    times_applied: usize,
    banned_until: usize,
    times_banned: usize,
}

impl Scheduler {
    /// Set the match limit after which a rule will be banned.
    /// Default: 1,000
    pub fn with_match_limit(self, match_limit: usize) -> Self {
        Self {
            match_limit,
            ..self
        }
    }

    /// Set the ban length.
    /// Default: 2 iterations
    pub fn with_ban_length(self, ban_length: usize) -> Self {
        Self { ban_length, ..self }
    }
}

impl Default for Scheduler {
    fn default() -> Self {
        Self {
            stats: Default::default(),
            match_limit: 100_000,
            ban_length: 1,
        }
    }
}

impl<L, N> RewriteScheduler<L, N> for Scheduler
    where
        L: Language,
        N: Analysis<L>,
{
    fn can_stop(&mut self, iteration: usize) -> bool {
        // let n_stats = self.stats.len();

        let mut banned: Vec<_> = self
            .stats
            .iter_mut()
            .filter(|(_, s)| s.banned_until > iteration)
            .collect();

        if banned.is_empty() {
            true
        } else {
            let min_ban = banned
                .iter()
                .map(|(_, s)| s.banned_until)
                .min()
                .expect("banned cannot be empty here");

            assert!(min_ban >= iteration);
            let delta = min_ban - iteration;

            let mut unbanned = vec![];
            for (name, s) in &mut banned {
                s.banned_until -= delta;
                if s.banned_until == iteration {
                    unbanned.push(name.as_str());
                }
            }

            assert!(!unbanned.is_empty());
            /*info!(
                "Banned {}/{}, fast-forwarded by {} to unban {}",
                banned.len(),
                n_stats,
                delta,
                unbanned.join(", "),
            );*/

            false
        }
    }

    fn search_rewrite(
        &mut self,
        iteration: usize,
        egraph: &EGraph<L, N>,
        rewrite: &Rewrite<L, N>,
    ) -> Vec<SearchMatches> {
        if let Some(limit) = self.stats.get_mut(rewrite.name()) {
            if iteration < limit.banned_until {
                /*debug!(
                    "Skipping {} ({}-{}), banned until {}...",
                    rewrite.name(),
                    limit.times_applied,
                    limit.times_banned,
                    limit.banned_until,
                );*/
                return vec![];
            }

            let matches = rewrite.search(egraph);
            let total_len: usize = matches.iter().map(|m| m.substs.len()).sum();
            if total_len > self.match_limit {
                limit.times_banned += 1;
                limit.banned_until = iteration + self.ban_length;
                /*info!(
                    "Banning {} ({}-{}) for {} iters: {} < {}",
                    rewrite.name(),
                    limit.times_applied,
                    limit.times_banned,
                    ban_length,
                    threshold,
                    total_len,
                );*/
                vec![]
            } else {
                limit.times_applied += 1;
                matches
            }
        } else {
            self.stats.insert(
                rewrite.name().into(),
                RuleStats {
                    times_applied: 0,
                    banned_until: 0,
                    times_banned: 0,
                },
            );
            rewrite.search(egraph)
        }
    }
}