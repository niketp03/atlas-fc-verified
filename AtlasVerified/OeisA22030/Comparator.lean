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

-- The two definitions of `a` are textually identical, but each compiles to its own
-- recursor, so `rfl` does not reduce one to the other. We prove the pointwise
-- equality instead, by the same recursion the definition uses. This is a strictly
-- stronger check than a textual diff: it would fail if the recurrences differed.
theorem a_eq : ∀ n, Atlas.OeisA22030.a n = OeisA22030.a n
  | 0 => rfl
  | 1 => rfl
  | (n + 2) => by
      have h0 := a_eq n
      have h1 := a_eq (n + 1)
      simp only [Atlas.OeisA22030.a, OeisA22030.a, h0, h1]


/-! ## Check 2 — FC's statement, in FC's own vocabulary, closed by the Atlas term. -/

theorem fc_statement_is_proved (n : ℕ) (hn : 4 ≤ n) :
    OeisA22030.a n
      = 4 * OeisA22030.a (n - 1) - OeisA22030.a (n - 3) + OeisA22030.a (n - 4) := by
  simpa only [a_eq] using Atlas.OeisA22030.conjecture n hn

end AtlasCompare.OeisA22030

#print axioms AtlasCompare.OeisA22030.fc_statement_is_proved
