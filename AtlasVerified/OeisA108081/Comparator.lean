/-
Comparator for OEIS A108081 (`count_words_in_x_is_a_shifted`).

Atlas file : `Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean`  (namespace `Atlas.OeisA108081`)
FC file    : `FormalConjectures/OEIS/108081.lean`  (namespace `OeisA108081`)
FC theorem : `OeisA108081.count_words_in_x_is_a_shifted`

Five definitions are shared, including the word-set `xN` the statement counts
and the sequence `a` it is compared against. Check 1 pins all of them.
-/

import AtlasVerified.OeisA108081.Solution
import FormalConjectures.OEIS.«108081»

open Nat

namespace AtlasCompare.OeisA108081

/-! ## Check 1 — every shared definition agrees definitionally. -/

example : Atlas.OeisA108081.Word = OeisA108081.Word := rfl
example : Atlas.OeisA108081.a = OeisA108081.a := rfl
example : Atlas.OeisA108081.l = OeisA108081.l := rfl
example : Atlas.OeisA108081.r = OeisA108081.r := rfl
example : Atlas.OeisA108081.xN = OeisA108081.xN := rfl


/-! ## Check 2 — FC's statement, in FC's own vocabulary, closed by the Atlas term. -/

theorem fc_statement_is_proved (n : ℕ) :
    n ≥ 1 → Set.ncard (OeisA108081.xN n) = OeisA108081.a (n - 1) :=
  Atlas.OeisA108081.count_words_in_x_is_a_shifted n

end AtlasCompare.OeisA108081

#print axioms AtlasCompare.OeisA108081.fc_statement_is_proved
