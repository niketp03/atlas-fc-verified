/-
Comparator for OEIS A211417 (`supercongruence`).

Atlas file : `Atlas/FC/OeisA211417_supercongruence_solution.lean`  (namespace `Atlas.OeisA211417`)
FC file    : `FormalConjectures/OEIS/211417.lean`  (namespace `OeisA211417`)
FC theorem : `OeisA211417.supercongruence`

Both files define the factorial-ratio sequence `a` independently, so Check 1
is load-bearing.
-/

import AtlasVerified.OeisA211417.Solution
import FormalConjectures.OEIS.«211417»

open Nat Int Finset

namespace AtlasCompare.OeisA211417

/-! ## Check 1 — the two definitions of the sequence agree definitionally. -/

example : Atlas.OeisA211417.a = OeisA211417.a := rfl


/-! ## Check 2 — FC's statement, in FC's own vocabulary, closed by the Atlas term. -/

theorem fc_statement_is_proved (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ ((OeisA211417.a (p ^ k) : ℤ) - (OeisA211417.a (p ^ (k - 1)) : ℤ)) :=
  Atlas.OeisA211417.supercongruence p k hp hp5 hk

end AtlasCompare.OeisA211417

#print axioms AtlasCompare.OeisA211417.fc_statement_is_proved
