/-
Comparator for OEIS A022030 (`conjecture`).

Atlas file : `Atlas/FC/OeisA22030_conjecture.lean`  (namespace `Atlas.OeisA22030`)
FC file    : `FormalConjectures/OEIS/22030.lean`  (namespace `OeisA22030`)
FC theorem : `OeisA22030.conjecture`

Both files define the sequence `a` independently. Check 1 is therefore
load-bearing: without it the Atlas proof could be about a different sequence.
-/

import AtlasVerified.OeisA22030.Solution
import FormalConjectures.OEIS.«22030»


namespace AtlasCompare.OeisA22030

/-! ## Check 1 — the two definitions of the sequence agree definitionally. -/

example : Atlas.OeisA22030.a = OeisA22030.a := rfl


/-! ## Check 2 — FC's statement, in FC's own vocabulary, closed by the Atlas term. -/

theorem fc_statement_is_proved (n : ℕ) (hn : 4 ≤ n) :
    OeisA22030.a n
      = 4 * OeisA22030.a (n - 1) - OeisA22030.a (n - 3) + OeisA22030.a (n - 4) :=
  Atlas.OeisA22030.conjecture n hn

end AtlasCompare.OeisA22030

#print axioms AtlasCompare.OeisA22030.fc_statement_is_proved
