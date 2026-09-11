import Mathlib
import EvalTools.Markers

/-!
# OEIS A108081 — counting X-words

`a(n) = ∑_{k=0}^n C(n+k-1, k) F(n-k+1)`, where `F` is Fibonacci. `XWord` is the
smallest set of integer words closed under the two operations `l` and `r`
described in A108081, and `xN n` is the set of X-words of length `n`. The
conjecture is that `|X_n| = a(n-1)` for `n ≥ 1`.

All of `a`, `Word`, `l`, `r`, `XWord`, `xN` and
`count_words_in_x_is_a_shifted` are vendored verbatim from
`FormalConjectures/OEIS/108081.lean` in `google-deepmind/formal-conjectures`
(namespace `OeisA108081`). Only the `@[category]` attribute, which is
formal-conjectures metadata, is dropped.

Note `XWord` is an *inductive predicate*. Two `inductive` declarations are
distinct constants however identical their constructors, so this definition
being a faithful copy is load-bearing for the statement meaning what FC means.

*References:*
- [A108081](https://oeis.org/A108081)
-/

namespace LeanEval.FormalConjectures.OeisA108081

open Nat

/-- The primary defining sequence `a`.
$a(n) = \sum_{k=0}^n \binom{n+k-1}{k} F(n-k+1)$, where $F(m)$ is the $m$-th Fibonacci number. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (n + k - 1).choose k * fib (n - k + 1)

/-- Words are finite sequences of integers. -/
abbrev Word := List ℤ

/-- `l w` is the word obtained by reversing `w` and subtracting 1 from every term. -/
def l (w : Word) : Word :=
  w.reverse.map (fun x => x - 1)

/-- `r w` is the word obtained by reversing `w` and adding 1 to every term. -/
def r (w : Word) : Word :=
  w.reverse.map (fun x => x + 1)

/--
`XWord` is the smallest set of words satisfying the inductive properties described in A108081.
-/
inductive XWord : Word → Prop
  | base : XWord [0]
  | step_left {u v : Word} (hu : XWord u) (hv : XWord v) : XWord (l u ++ v)
  | step_right {u v : Word} (hu : XWord u) (hv : XWord v) : XWord (u ++ r v)

/-- `xN n` is the set of words in `XWord` of length `n`. -/
def xN (n : ℕ) : Set Word :=
  {w : Word | XWord w ∧ w.length = n}

/-- The number of X-words of length `n` is `a (n - 1)`, for `n ≥ 1`. -/
@[eval_problem]
theorem oeis_a108081_count_words (n : ℕ) :
    n ≥ 1 → Set.ncard (xN n) = a (n - 1) := by
  sorry

end LeanEval.FormalConjectures.OeisA108081
