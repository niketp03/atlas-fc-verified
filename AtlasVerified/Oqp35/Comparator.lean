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

-- Each of these is stated *applied*: most carry implicit `{n d : ℕ}`, which an
-- unapplied equation leaves undetermined.
example (n d : ℕ) : Atlas.OpenQuantumProblem35.Config n d = OpenQuantumProblem35.Config n d := rfl
example (n d : ℕ) : Atlas.OpenQuantumProblem35.StateVector n d = OpenQuantumProblem35.StateVector n d := rfl
example (n d : ℕ) (ψ : OpenQuantumProblem35.Config n d → ℂ) :
    Atlas.OpenQuantumProblem35.mkStateVector ψ = OpenQuantumProblem35.mkStateVector ψ := rfl
example (n d : ℕ) (ψ : OpenQuantumProblem35.StateVector n d) :
    Atlas.OpenQuantumProblem35.IsNormalized ψ = OpenQuantumProblem35.IsNormalized ψ := rfl
example (n d : ℕ) (π : Equiv.Perm (Fin n)) (x : OpenQuantumProblem35.Config n d) :
    Atlas.OpenQuantumProblem35.permuteConfig π x = OpenQuantumProblem35.permuteConfig π x := rfl
example (n d : ℕ) (π : Equiv.Perm (Fin n)) (ψ : OpenQuantumProblem35.StateVector n d) :
    Atlas.OpenQuantumProblem35.permuteState π ψ = OpenQuantumProblem35.permuteState π ψ := rfl
example (n d : ℕ) (x : OpenQuantumProblem35.Config n d) :
    Atlas.OpenQuantumProblem35.IsConstantConfig x = OpenQuantumProblem35.IsConstantConfig x := rfl
example (n d m : ℕ) (hm : m ≤ n) (x : OpenQuantumProblem35.Config m d) (y : OpenQuantumProblem35.Config (n - m) d) :
    Atlas.OpenQuantumProblem35.combineFirst m hm x y = OpenQuantumProblem35.combineFirst m hm x y := rfl
example (n d m : ℕ) (hm : m ≤ n) (ψ : OpenQuantumProblem35.StateVector n d) :
    Atlas.OpenQuantumProblem35.reducedDensityFirst m hm ψ = OpenQuantumProblem35.reducedDensityFirst m hm ψ := rfl
example (m d : ℕ) : Atlas.OpenQuantumProblem35.maximallyMixed m d = OpenQuantumProblem35.maximallyMixed m d := rfl
example (n d m : ℕ) (hm : m ≤ n) (ψ : OpenQuantumProblem35.StateVector n d) :
    Atlas.OpenQuantumProblem35.HasMaximallyMixedFirstReduction m hm ψ
      = OpenQuantumProblem35.HasMaximallyMixedFirstReduction m hm ψ := rfl
example (n d : ℕ) (ψ : OpenQuantumProblem35.StateVector n d) : Atlas.OpenQuantumProblem35.IsAME ψ = OpenQuantumProblem35.IsAME ψ := rfl
example (n d : ℕ) : Atlas.OpenQuantumProblem35.ExistsAME n d = OpenQuantumProblem35.ExistsAME n d := rfl


/-! ## Check 2 — FC's statement, in FC's own vocabulary, closed by the Atlas term.

`answer(sorry)` is instantiated to `True`; see the note above. -/

theorem fc_statement_is_proved : True ↔ OpenQuantumProblem35.ExistsAME 9 10 :=
  ⟨fun _ => Atlas.OpenQuantumProblem35.ame_9_10_open, fun _ => trivial⟩

end AtlasCompare.Oqp35

#print axioms AtlasCompare.Oqp35.fc_statement_is_proved
