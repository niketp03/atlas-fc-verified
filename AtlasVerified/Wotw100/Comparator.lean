/-
Comparator for Written on the Wall II, Graph Conjecture 100.

Atlas file : `Atlas/FC/WrittenOnTheWallII_GraphConjecture100_conjecture100.lean`  (namespace `Atlas.WrittenOnTheWallII.GraphConjecture100`)
FC file    : `FormalConjectures/WrittenOnTheWallII/GraphConjecture100.lean`  (namespace `WrittenOnTheWallII.GraphConjecture100`)
FC theorem : `WrittenOnTheWallII.GraphConjecture100.conjecture100`

The Atlas statement is byte-for-byte identical to FC's, and every notion in it
(`indepNum`, `indepNeighborsCard`, `degreeL2Norm`) comes from
FormalConjecturesForMathlib rather than being redefined locally. Check 2 is decisive.
-/

import AtlasVerified.Wotw100.Solution
import FormalConjectures.WrittenOnTheWallII.GraphConjecture100

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

namespace AtlasCompare.Wotw100

/-! ## Check — FC's statement, verbatim, closed by the Atlas term. -/

theorem fc_statement_is_proved (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤ ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ :=
  Atlas.WrittenOnTheWallII.GraphConjecture100.conjecture100 G h

end AtlasCompare.Wotw100

#print axioms AtlasCompare.Wotw100.fc_statement_is_proved
