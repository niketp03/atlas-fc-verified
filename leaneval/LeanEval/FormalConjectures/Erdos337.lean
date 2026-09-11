import Mathlib
import EvalTools.Markers

/-!
# Erdős 337 — the Ruzsa–Turjányi variant

If `A ⊆ ℕ` is an asymptotic additive basis whose counting function is `o(N)`, then

  `|(A + A) ∩ [1, 2N]| / |A ∩ [1, N]| → ∞`.

Ruzsa and Turjányi proved the corresponding statement for the threefold sumset
`(A + A + A) ∩ [1, 3N]`; this twofold form is their conjecture.

Vendored from `google-deepmind/formal-conjectures`:

* `erdos_337.variants.ruzsa_turjanyi` is verbatim from
  `FormalConjectures/ErdosProblems/337.lean` (namespace `Erdos337`);
* `IsAsymptoticMulBasisOfOrder` and `IsAsymptoticMulBasis` are verbatim from
  `FormalConjecturesForMathlib/Combinatorics/Additive/Basis.lean` (namespace `Set`).

Note the `@[to_additive]` attributes. The statement is about
`Set.IsAsymptoticAddBasis`, a name that appears nowhere in formal-conjectures'
source text — it is *generated* from the multiplicative definition by
`to_additive`. Carrying the multiplicative pair over with its attributes intact
is what makes the generated additive name here the same definition as FC's,
rather than a hand-written lookalike.

Only the `@[category]` attribute, which is formal-conjectures metadata, is dropped.
-/

namespace LeanEval.FormalConjectures.Erdos337

open Filter Set Asymptotics
open scoped Pointwise

namespace Set

variable {M : Type*} [CommMonoid M]

/-- A set `A : Set M` is an asymptotic multiplicative basis of order `n` if the
elements that can be expressed as a product of `n` elements lying in `A` is cofinite. -/
@[to_additive
/-- A set `A : Set M` is an asymptotic additive basis of order `n` if the elements that
can be expressed as a sum of `n` elements lying in `A` is cofinite. -/]
def IsAsymptoticMulBasisOfOrder (A : _root_.Set M) (n : ℕ) : Prop :=
  ∀ᶠ a in cofinite, a ∈ A ^ n

/-- An asymptotic multiplicative basis of some order. -/
@[to_additive /-- An asymptotic additive basis of some order. -/]
def IsAsymptoticMulBasis (A : _root_.Set M) : Prop := ∃ n, IsAsymptoticMulBasisOfOrder A n

end Set

/--
Ruzsa–Turjányi: for every asymptotic additive basis `A ⊆ ℕ` with
`|A ∩ [1,N]| = o(N)`, the ratio `|(A+A) ∩ [1,2N]| / |A ∩ [1,N]|` tends to infinity.
-/
@[eval_problem]
theorem erdos_337_ruzsa_turjanyi :
    ∀ A : _root_.Set ℕ, Set.IsAsymptoticAddBasis A →
      (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) →
      Tendsto (fun N : ℕ ↦
          (((A + A) ∩ Icc 1 (2 * N)).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ))
        atTop atTop := by
  sorry

end LeanEval.FormalConjectures.Erdos337
