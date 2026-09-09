/-
Comparator for Green's Open Problem 25 (`green_25.upper`).

Atlas file : `Atlas/FC/Green25_upper_solution.lean`  (namespace `Atlas.Green25`)
FC file    : `FormalConjectures/GreensOpenProblems/25.lean`  (namespace `Green25`)
FC theorem : `Green25.green_25.upper`

Two deviations from FC's statement, in opposite directions.

  * FC writes `let ans := answer(sorry)`; Atlas writes `∃ candidateAnswer`. Replacing a
    determination by an existential is *weaker* in FC's idiom — see `AGENTS.md`, "a
    tautological term inside `answer()` is not a mathematical solution". The construction
    does produce an explicit function, so this is presentational; `Improved.lean` in this
    directory names it and discharges FC's statement verbatim.
  * FC's third conjunct is `¬ ∀ᶠ N, Property25 …`; Atlas proves `∀ᶠ N, ¬ Property25 …`,
    which is *stronger*.

Check 2 below states the Atlas shape in FC's vocabulary. The verbatim FC statement is
discharged in `Improved.lean`.
-/

import AtlasVerified.Green25.Solution
import FormalConjectures.GreensOpenProblems.«25»

open Asymptotics Filter Finset

namespace AtlasCompare.Green25

/-! ## Check 1 — the shared definitions agree definitionally. -/

example : Atlas.Green25.Property25 = Green25.Property25 := rfl
example : Atlas.Green25.bestUpper = Green25.bestUpper := rfl


/-! ## Check 2 — the Atlas shape, in FC's own vocabulary, closed by the Atlas term. -/

theorem fc_statement_is_proved :
    ∃ candidateAnswer : ℕ → ℕ,
      let ans := (candidateAnswer : ℕ → ℕ)
      (∀ᶠ N in atTop, 1 ≤ ans N ∧ ans N ≤ N) ∧
      (fun N => (ans N : ℝ)) =o[atTop] Green25.bestUpper ∧
      ∀ᶠ N in atTop, ¬ Green25.Property25 (ans N) N :=
  Atlas.Green25.green_25.upper

end AtlasCompare.Green25

#print axioms AtlasCompare.Green25.fc_statement_is_proved
