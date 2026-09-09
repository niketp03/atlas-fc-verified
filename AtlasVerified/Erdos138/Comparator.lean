/-
Comparator for Erdos 138 (`erdos_138.variants.dvd_two_pow`).

Atlas file : `Atlas/FC/Erdos138_dvd_two_pow_solution.lean`  (namespace `Atlas.Erdos138`)
FC file    : `FormalConjectures/ErdosProblems/138.lean`  (namespace `Erdos138`)
FC theorem : `Erdos138.erdos_138.variants.dvd_two_pow`

Note on the `answer()` slot. FC states `answer(sorry) ↔ Tendsto …`, i.e. the
answer is a *proposition* to be determined. The Atlas file proves the right-hand side
outright (`W k / 2 ^ k → ∞`), so the answer is `True`, and we discharge FC's iff with
that instantiation. Filling `answer()` with `True` is exactly the content of proving
the right-hand side, so this is a faithful reading rather than a dodge.
-/

import AtlasVerified.Erdos138.Solution
import FormalConjectures.ErdosProblems.«138»

open Nat Filter

namespace AtlasCompare.Erdos138

/-! ## Check 1 — the shared definitions agree definitionally. -/

example : Atlas.Erdos138.W = Erdos138.W := rfl
example : Atlas.Erdos138.monoAPNumber = Erdos138.monoAPNumber := rfl
example : Atlas.Erdos138.monoAP_guarantee_set = Erdos138.monoAP_guarantee_set := rfl


/-! ## Check 2 — FC's statement, in FC's own vocabulary, closed by the Atlas term.

`answer(sorry)` is instantiated to `True`; see the note above. -/

theorem fc_statement_is_proved :
    True ↔ atTop.Tendsto (fun k => ((Erdos138.W k : ℚ) / (2 ^ k))) atTop :=
  ⟨fun _ => Atlas.Erdos138.erdos_138.variants.dvd_two_pow, fun _ => trivial⟩

end AtlasCompare.Erdos138

#print axioms AtlasCompare.Erdos138.fc_statement_is_proved
