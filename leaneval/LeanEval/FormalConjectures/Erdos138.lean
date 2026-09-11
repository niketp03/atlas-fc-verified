import Mathlib
import EvalTools.Markers

/-!
# Erdős 138 — does `W(k) / 2^k → ∞`?

`W(k)` is the van der Waerden number for two colours: the least `N` such that
every 2-colouring of `{1, …, N}` contains a monochromatic arithmetic
progression of length `k`. In [Er80] Erdős asks whether `W(k)/2^k → ∞`.

Vendored from `google-deepmind/formal-conjectures`:

* `monoAP_guarantee_set`, `monoAPNumber` and `W` are verbatim from
  `FormalConjectures/ErdosProblems/138.lean` (namespace `Erdos138`);
* `Set.IsAPOfLengthWith`, `Set.IsAPOfLength` and `ContainsMonoAPofLength` are
  verbatim from `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`.

## A deliberate deviation in statement shape

FC states this as `erdos_138.variants.dvd_two_pow : answer(sorry) ↔ P`, where
`answer(…)` is formal-conjectures' own marker for "the solver must also supply
the answer". That machinery does not exist outside formal-conjectures, and a
lean-eval Challenge has to be a closed proposition. The statement below is `P`
itself:

  `atTop.Tendsto (fun k => ((W k : ℚ) / 2 ^ k)) atTop`

which is the same choice the hand-written comparator in this repository records
for Erdos138 — proving `P` outright instantiates the answer to `True`. It is a
faithful reading, but it *is* an instantiation choice, and it is the one place
this Challenge is not a literal transcription of FC's theorem.

*References:*
- [erdosproblems.com/138](https://www.erdosproblems.com/138)
- [Er80] Erdős, A survey of problems in combinatorial number theory.
-/

namespace LeanEval.FormalConjectures.Erdos138

open Nat Filter

variable {α : Type*} [AddCommMonoid α]

/-- A set `S` is an arithmetic progression of length `l` with first term `a` and
difference `d`. -/
def Set.IsAPOfLengthWith (s : _root_.Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/-- A set `S` is an arithmetic progression of length `l`, for some first term and
difference. -/
def Set.IsAPOfLength (s : _root_.Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, Set.IsAPOfLengthWith s l a d

/-- A colouring of `M` contains a monochromatic arithmetic progression of length `k`. -/
def ContainsMonoAPofLength {κ : Type} [Finite κ] {M : _root_.Set α}
    (coloring : M → κ) (k : ℕ) : Prop :=
  ∃ c : κ, ∃ ap : _root_.Set M, Set.IsAPOfLength ((·.1) '' ap) k ∧
    ∀ m ∈ ap, coloring m = c

/--
The set of natural numbers that guarantee a monochromatic arithmetic progression.
-/
def monoAP_guarantee_set (r k : ℕ) : _root_.Set ℕ :=
  { N | ∀ coloring : Finset.Icc 1 N → Fin r, ContainsMonoAPofLength coloring k }

/-- The **van der Waerden number**. -/
noncomputable def monoAPNumber (r k : ℕ) : ℕ := sInf (monoAP_guarantee_set r k)

/-- The van der Waerden number for 2 colours, `W(k)`. -/
noncomputable abbrev W : ℕ → ℕ := monoAPNumber 2

/--
Erdős 138 (the `W(k)/2^k` variant): `W(k)/2^k → ∞`.
-/
@[eval_problem]
theorem erdos_138_dvd_two_pow :
    atTop.Tendsto (fun k => ((W k : ℚ) / (2 ^ k))) atTop := by
  sorry

end LeanEval.FormalConjectures.Erdos138
