import Mathlib
import EvalTools.Markers

/-!
# OEIS A211417 — a supercongruence for `(30n)! n! / ((15n)! (10n)! (6n)!)`

`a(n) = (30n)! n! / ((15n)! (10n)! (6n)!)` is an integral factorial ratio
sequence. The conjecture is the supercongruence

  `a(p^k) ≡ a(p^(k-1))  (mod p^(3k))`

for every prime `p ≥ 5` and every positive integer `k`.

`a` and `supercongruence` are vendored verbatim from
`FormalConjectures/OEIS/211417.lean` in `google-deepmind/formal-conjectures`
(namespace `OeisA211417`). Only the `@[category]` attribute, which is
formal-conjectures metadata, is dropped.

*References:*
- [A211417](https://oeis.org/A211417)
- Supercongruence observed by Peter Bala, Jan 24 2020
-/

namespace LeanEval.FormalConjectures.OeisA211417

/--
Integral factorial ratio sequence:
$$a(n) = \frac{(30n)! n!}{(15n)! (10n)! (6n)!}$$
-/
def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

/--
Supercongruence: `a(p^k) ≡ a(p^(k-1)) (mod p^(3k))` for any prime `p ≥ 5` and
any positive integer `k`.
-/
@[eval_problem]
theorem oeis_a211417_supercongruence (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ)) := by
  sorry

end LeanEval.FormalConjectures.OeisA211417
