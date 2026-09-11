import Mathlib
import EvalTools.Markers

/-!
# Green's Open Problem 25 — improving the [ESS89] upper bound

`Property25 k N` says: every partition of `[1, N]` into `k` parts has
`|⋃ᵢ (Aᵢ +̂ Aᵢ)| ≥ N/10`, where `+̂` is the restricted sumset. Green asks for
which `k` this holds. The best-known upper bound is `bestUpper N = N / log N`
[ESS89]; the conjecture is that it can be lowered.

Vendored from `google-deepmind/formal-conjectures`:

* `Property25` and `bestUpper` are verbatim from
  `FormalConjectures/GreensOpenProblems/25.lean` (namespace `Green25`);
* `Finset.restrictedSumset` from
  `FormalConjecturesForMathlib/Combinatorics/Additive/RestrictedSumset.lean`.

## A deliberate deviation in statement shape

FC writes `green_25.upper` as

```
let ans := (answer(sorry) : ℕ → ℕ)
(∀ᶠ N in atTop, 1 ≤ ans N ∧ ans N ≤ N) ∧ … ∧ ¬ ∀ᶠ N in atTop, Property25 (ans N) N
```

`answer(…)` is formal-conjectures machinery for "the solver must also supply the
witness", and it does not exist outside that repository. The Challenge below
closes the slot existentially, `∃ ans : ℕ → ℕ, …`, which is what the marker
means operationally. Note that this is *weaker* than FC's idiom, where a
determination is expected rather than a mere existence claim — FC's `AGENTS.md`
is explicit that "a tautological term inside `answer()` is not a mathematical
solution". The construction used to discharge this does produce an explicit
function, so nothing is lost in substance; but the Challenge as stated here does
not force that.

The third conjunct is FC's own `¬ ∀ᶠ N, Property25 …`, not the stronger
`∀ᶠ N, ¬ Property25 …`.

*References:*
- [Gr24] Green, Ben. "100 open problems." (2024), problem 25.
- [ESS89] Erdős, Sárközy and Sós, "On a conjecture of Roth and some related problems I."
-/

namespace LeanEval.FormalConjectures.Green25

open Asymptotics Filter Finset

/--
The restricted sumset of a set `S`, denoted `S +̂ S`, is
`{s₁ + s₂ : s₁, s₂ ∈ S, s₁ ≠ s₂}`.
-/
def restrictedSumset {α : Type*} [Add α] [DecidableEq α] (S : Finset α) : Finset α :=
  S.offDiag.image (fun p => p.1 + p.2)

/--
For which `k` is it true that whenever we partition `[N] = A₁ ∪ … ∪ A_k`,
`|⋃ᵢ (Aᵢ +̂ Aᵢ)| ≥ N/10`?
-/
def Property25 (k N : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ N ∧
  ∀ P : Finpartition (Icc 1 N), #P.parts = k →
  10 * #(P.parts.biUnion restrictedSumset) ≥ N

/-- The best-known upper bound [ESS89]. -/
noncomputable def bestUpper (N : ℕ) : ℝ := (N : ℝ) / Real.log N

/--
Green 25, upper-bound variant: the [ESS89] bound `N / log N` can be lowered.
There is a partition size `k(N) = o(N / log N)` for which `Property25` fails.
-/
@[eval_problem]
theorem green_25_upper :
    ∃ ans : ℕ → ℕ,
      (∀ᶠ N in atTop, 1 ≤ ans N ∧ ans N ≤ N) ∧
      (fun N => (ans N : ℝ)) =o[atTop] bestUpper ∧
      ¬ ∀ᶠ N in atTop, Property25 (ans N) N := by
  sorry

end LeanEval.FormalConjectures.Green25
