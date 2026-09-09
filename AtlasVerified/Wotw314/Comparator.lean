/-
Comparator for Written on the Wall II, Graph Conjecture 314.

Atlas file : `Atlas/FC/WrittenOnTheWallII_GraphConjecture314_conjecture314.lean`  (namespace `Atlas.WrittenOnTheWallII.GraphConjecture314`)
FC file    : `FormalConjectures/WrittenOnTheWallII/GraphConjecture314.lean`  (namespace `WrittenOnTheWallII.GraphConjecture314`)
FC theorem : `WrittenOnTheWallII.GraphConjecture314.conjecture314`

`largestInducedPathSize` appears in the hypotheses of the statement and is
defined on both sides, so Check 1 is load-bearing: a weaker notion of induced path
length would weaken the hypothesis and so strengthen the theorem spuriously.
-/

import AtlasVerified.Wotw314.Solution
import FormalConjectures.WrittenOnTheWallII.GraphConjecture314

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

namespace AtlasCompare.Wotw314

/-! ## Check 1 — the shared definition agrees definitionally. -/

example : Atlas.WrittenOnTheWallII.GraphConjecture314.largestInducedPathSize = WrittenOnTheWallII.GraphConjecture314.largestInducedPathSize := rfl


/-! ## Check 2 — FC's statement, in FC's own vocabulary, closed by the Atlas term. -/

theorem fc_statement_is_proved [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : WrittenOnTheWallII.GraphConjecture314.largestInducedPathSize G ≤ 4) :
    IsWellTotallyDominated G :=
  Atlas.WrittenOnTheWallII.GraphConjecture314.conjecture314 G hG hTriFree hPath

end AtlasCompare.Wotw314

#print axioms AtlasCompare.Wotw314.fc_statement_is_proved
