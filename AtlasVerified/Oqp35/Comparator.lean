/-
Comparator for Open Quantum Problem 35 (`ame_9_10_open`) — AME(9,10).

Atlas file : `Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean`  (namespace `Atlas.OpenQuantumProblem35`)
FC file    : `FormalConjectures/OpenQuantumProblems/35.lean`  (namespace `OpenQuantumProblem35`)
FC theorem : `OpenQuantumProblem35.ame_9_10_open`

This is the substantive one: thirteen definitions are shared, and the whole
meaning of the claim rests on them (what a state vector is, what `IsAME` means, what
`ExistsAME` quantifies over). Check 1 pins every one.

Note on the `answer()` slot. FC states `answer(sorry) ↔ ExistsAME 9 10`. The Atlas file
proves `ExistsAME 9 10` outright, so the answer is `True`.
-/

import AtlasVerified.Oqp35.Solution
import FormalConjectures.OpenQuantumProblems.«35»

open scoped BigOperators

namespace AtlasCompare.Oqp35

/-! ## Check 1 — every shared definition agrees definitionally. -/

example : Atlas.OpenQuantumProblem35.Config = OpenQuantumProblem35.Config := rfl
example : Atlas.OpenQuantumProblem35.StateVector = OpenQuantumProblem35.StateVector := rfl
example : Atlas.OpenQuantumProblem35.mkStateVector = OpenQuantumProblem35.mkStateVector := rfl
example : Atlas.OpenQuantumProblem35.IsNormalized = OpenQuantumProblem35.IsNormalized := rfl
example : Atlas.OpenQuantumProblem35.permuteConfig = OpenQuantumProblem35.permuteConfig := rfl
example : Atlas.OpenQuantumProblem35.permuteState = OpenQuantumProblem35.permuteState := rfl
example : Atlas.OpenQuantumProblem35.IsConstantConfig = OpenQuantumProblem35.IsConstantConfig := rfl
example : Atlas.OpenQuantumProblem35.combineFirst = OpenQuantumProblem35.combineFirst := rfl
example : Atlas.OpenQuantumProblem35.reducedDensityFirst = OpenQuantumProblem35.reducedDensityFirst := rfl
example : Atlas.OpenQuantumProblem35.maximallyMixed = OpenQuantumProblem35.maximallyMixed := rfl
example : Atlas.OpenQuantumProblem35.HasMaximallyMixedFirstReduction = OpenQuantumProblem35.HasMaximallyMixedFirstReduction := rfl
example : Atlas.OpenQuantumProblem35.IsAME = OpenQuantumProblem35.IsAME := rfl
example : Atlas.OpenQuantumProblem35.ExistsAME = OpenQuantumProblem35.ExistsAME := rfl


/-! ## Check 2 — FC's statement, in FC's own vocabulary, closed by the Atlas term.

`answer(sorry)` is instantiated to `True`; see the note above. -/

theorem fc_statement_is_proved : True ↔ OpenQuantumProblem35.ExistsAME 9 10 :=
  ⟨fun _ => Atlas.OpenQuantumProblem35.ame_9_10_open, fun _ => trivial⟩

end AtlasCompare.Oqp35

#print axioms AtlasCompare.Oqp35.fc_statement_is_proved
