/-
Comparator for Erdos 337 (`erdos_337.variants.ruzsa_turjanyi`).

Atlas file : `Atlas/FC/Erdos337_ruzsa_turjanyi_solution.lean`  (namespace `Atlas.Erdos337`)
FC file    : `FormalConjectures/ErdosProblems/337.lean`  (namespace `Erdos337`)
FC theorem : `Erdos337.erdos_337.variants.ruzsa_turjanyi`

The Atlas statement is byte-for-byte identical to FC's, and neither side
introduces auxiliary definitions that enter the statement — every notion in it
(`Set.IsAsymptoticAddBasis`, `ncard`, `=o`) comes from Mathlib or
FormalConjecturesForMathlib. So Check 2 alone is decisive here.
-/

import AtlasVerified.Erdos337.Solution
import FormalConjectures.ErdosProblems.«337»

open Filter Set Asymptotics
open scoped Pointwise

namespace AtlasCompare.Erdos337

/-! ## Check — FC's statement, verbatim, closed by the Atlas term. -/

theorem fc_statement_is_proved :
    ∀ A : Set ℕ, A.IsAsymptoticAddBasis →
      (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) →
      Tendsto (fun N : ℕ ↦
          (((A + A) ∩ Icc 1 (2 * N)).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ))
        atTop atTop :=
  Atlas.Erdos337.erdos_337.variants.ruzsa_turjanyi

end AtlasCompare.Erdos337

#print axioms AtlasCompare.Erdos337.fc_statement_is_proved
