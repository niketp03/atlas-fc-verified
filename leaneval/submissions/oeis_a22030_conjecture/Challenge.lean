import ChallengeDeps

open LeanEval.FormalConjectures.OeisA22030

theorem oeis_a22030_conjecture (n : ℕ) (hn : 4 ≤ n) :
    a n = 4 * a (n - 1) - a (n - 3) + a (n - 4) := by
  sorry
