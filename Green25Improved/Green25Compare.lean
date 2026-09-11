/-
Comparator: relates the improved Green 25 construction to the statement recorded
in `FormalConjectures.GreensOpenProblems.«25»`.

This file is a verification harness, not a problem file. Every declaration here
either typechecks (the check passes) or does not (the check fails).
-/

import FormalConjectures.GreensOpenProblems.«25»
import FormalConjectures.GreensOpenProblems.Green25Ladder

open Filter Asymptotics Finset

namespace Green25Compare

/-! ## Check 1 — the two files talk about the same objects.

`rfl` here is definitional equality, which is stronger than a textual diff: it
would still succeed under reformatting, and it fails if any definition drifted. -/

example : Green25Atlas.Property25 = Green25.Property25 := rfl
example : Green25Atlas.bestUpper = Green25.bestUpper := rfl
example : Green25Atlas.strongUpper = Green25.improvedUpper := rfl

/-! ## Check 2 — the proved theorem has exactly the type Formal Conjectures states.

The statement below is written against `Green25.*` (the Formal Conjectures
namespace) and is closed by the term from the work files directly. If this
elaborates, the proof really does inhabit the repository's proposition. -/

theorem fc_statement_is_proved :
    ∃ k : ℕ → ℕ,
      (∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N) ∧
      (fun N => (k N : ℝ)) =O[atTop] Green25.improvedUpper ∧
      ∀ᶠ N in atTop, ¬ Green25.Property25 (k N) N :=
  Green25Atlas.green_25.variants.upper_exp_sqrt_log

/-! ## Check 3 — the statement is not vacuous.

`Property25 k N` is a conjunction whose first two clauses are `1 ≤ k` and
`k ≤ N`. So `¬ Property25 (k N) N` could in principle be satisfied cheaply, by
choosing an out-of-range `k`. Here we discharge that worry: on the eventual set
the size constraints *do* hold, so the failure has to come from the third
clause, and we extract the witnessing partition. This is the real combinatorial
content of the theorem. -/

theorem witness_partition_exists :
    ∃ k : ℕ → ℕ, ∀ᶠ N in atTop,
      1 ≤ k N ∧ k N ≤ N ∧
      ∃ P : Finpartition (Icc 1 N), #P.parts = k N ∧
        10 * #(P.parts.biUnion Finset.restrictedSumset) < N := by
  obtain ⟨k, hsize, _, hbad⟩ := Green25Atlas.green_25.variants.upper_exp_sqrt_log
  refine ⟨k, ?_⟩
  filter_upwards [hsize, hbad] with N h1 h2
  refine ⟨h1.1, h1.2, ?_⟩
  by_contra hcon
  push_neg at hcon
  exact h2 ⟨h1.1, h1.2, fun P hP => hcon P hP⟩

/-! ## Check 4 — the improvement is a genuine improvement, not a restatement.

The part count really does grow more slowly than the published `N / log N`, and
more slowly than the `N / (log N)^2` that the same construction reaches at the
parameter the Atlas file publishes. -/

example : Green25.improvedUpper =o[atTop] Green25.bestUpper :=
  Green25Ladder.strongUpper_isLittleO_bestUpper

example : Green25.improvedUpper =o[atTop] Green25Atlas.improvedUpper :=
  Green25Ladder.strongUpper_isLittleO_logSq

end Green25Compare

/-! ## Check 5 — axiom audit.

The proved theorems must rest only on the three standard axioms. The Formal
Conjectures copy is expected to report `sorryAx`: it is a statement repository,
and the placeholder is deliberate. -/

#print axioms Green25Atlas.green_25.variants.upper_exp_sqrt_log
#print axioms Green25Compare.fc_statement_is_proved
#print axioms Green25Compare.witness_partition_exists
#print axioms Green25Ladder.fc_green_25_upper_answered
#print axioms Green25.green_25.variants.upper_exp_sqrt_log
