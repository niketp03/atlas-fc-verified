import Mathlib
import EvalTools.Markers

/-!
# OEIS A022030 — a nonlinear recurrence satisfies a linear one

For even `n`, `a (n+2)` is the greatest integer such that `a (n+2) / a (n+1) < a (n+1) / a n`;
for odd `n`, the least integer such that `a (n+2) / a (n+1) > a (n+1) / a n`;
`a 0 = 4`, `a 1 = 16`.

The conjecture is that this nonlinearly-defined sequence satisfies the *linear*
recurrence `a n = 4 * a (n-1) - a (n-3) + a (n-4)` for `n ≥ 4`.

The definition of `a` below is verbatim from
`FormalConjectures/OEIS/22030.lean` in `google-deepmind/formal-conjectures`
(`namespace OeisA22030`); only the `@[category]` attribute, which is
formal-conjectures metadata, is dropped.

*References:*
- [A022030](https://oeis.org/A022030)
- Conjecture due to Colin Barker, Feb 16 2012
-/

namespace LeanEval.FormalConjectures.OeisA22030

/--
For even $n$, $a(n+2)$ is the greatest integer such that $a(n+2)/a(n+1) < a(n+1)/a(n)$;
for odd $n$, the least integer such that $a(n+2)/a(n+1) > a(n+1)/a(n)$;
$a(0) = 4, a(1) = 16$.
-/
def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 4
  | 1 => 16
  | n + 2 =>
    if Even n then
      (a (n + 1) ^ 2 + a n - 1) / a n - 1
    else
      (a (n + 1) ^ 2) / a n + 1

/-- Conjecture: $a(n) = 4 a(n-1) - a(n-3) + a(n-4)$. -/
@[eval_problem]
theorem oeis_a22030_conjecture (n : ℕ) (hn : 4 ≤ n) :
    a n = 4 * a (n - 1) - a (n - 3) + a (n - 4) := by
  sorry

end LeanEval.FormalConjectures.OeisA22030
