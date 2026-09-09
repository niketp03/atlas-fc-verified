# Changes made to the Atlas sources

Every edit to the nine `Atlas/FC/` files is listed here. The originals are at
`facebookresearch/atlas-lean` @ `prepare-atlas-v2` (`223d8bc`); each `Solution.lean`
carries a provenance banner naming the file it came from.

Nothing below changes a statement or closes a mathematical gap. Every entry is
tactic-level drift against the Mathlib pinned by formal-conjectures (`v4.33.1`).

## Mechanical, applied to all nine

**Namespace rename `X` → `Atlas.X`.** Each Atlas file opens the *same* namespace as
the formal-conjectures file it targets (`namespace Green25` in both, `namespace
OeisA22030` in both, and so on), so each carries its own copy of the definitions the
statement is about. A comparator has to import both and tell those copies apart,
which is impossible while they share a namespace. The rename touches only the
`namespace` and `end` lines; no file contained a self-qualified reference.

`Erdos138_dvd_two_pow_solution.lean` had no closing `end` (the namespace ran to
end-of-file); one was added.

## Green25 — 1 fix

In `complemented_digit_partition`'s injectivity step:

```lean
-- was
simpa [f, encodeVector] using congrArg (fun n => n - 1) hbc
-- now
have hbc' : (finFunctionFinEquiv (flipVector Q r v b) : ℕ) + 1
    = (finFunctionFinEquiv (flipVector Q r v c) : ℕ) + 1 := hbc
omega
```

`encodeVector v = (finFunctionFinEquiv v : ℕ) + 1`, so the proof strips the `+ 1`
with `congrArg (· - 1)` and relies on `simp` cancelling `x + 1 - 1`. It no longer
does. This was the only error in the file.

## Wotw100 — 1 fix (2 sites)

`Finset.filter_card_add_filter_neg_card_eq_card` no longer exists; it is now
`Finset.card_filter_add_card_filter_not`, with the same shape and the same named
arguments (`s`, `p`).

## OeisA108081 — 2 fixes (8 sites)

`Relation.ReflTransGen.lift` changed shape. It used to take the chain as its last
explicit argument; it now returns a relation inequality:

```lean
theorem ReflTransGen.lift {p : β → β → Prop} (f : α → β) (h : r ≤ (p on f)) :
    ReflTransGen r ≤ (ReflTransGen p on f)
```

So every call site needs the two endpoints supplied before the chain:
`… lift f h hw` → `… lift f h _ _ hw`. The result then lands in `Function.onFun …`,
so `Function.onFun` had to be added to the two surrounding `simpa` sets.

`Finset.mem_antidiagonal` is now a field of the `Finset.HasAntidiagonal` class and no
longer unifies at the call site; replaced with `have hij' : i + j = m := by simpa
using hij`, which goes through the `@[simp]` form.

## Erdos138 — 15 fixes

1-2. `simp` no longer reduces `algebraMap (ZMod 2) K 0` to `0` (resp. `1` to `1`)
after `fin_cases`. Replaced `simpa using hz.symm` with `rw [← hz]; exact map_zero _`
(resp. `map_one _`), which goes through the hypothesis directly.

3-5. Three `rw [hz]` / `rw [hs]` / `rw [hz, hc]` steps stopped matching the sum
`∑ i, if ↑i = n then -P.coeff ↑i else 0` — the pattern and the target differ only in
the decidability instance, which `rw` matches syntactically. Folded each into the
following `simp`, which matches up to reducible defeq.

6. `recurrenceMap_charPoly`: `simp` now leaves an alpha-equivalent goal
`∑ i, monomial ↑i (f (E.coeffs i)) = ∑ x, monomial ↑x (f (E.coeffs x))`; added `rfl`.

7. `linearMap_solution`: `simpa … using hh` failed with the two types *displaying
identically* (an instance-path mismatch introduced by simping the goal as well as the
hypothesis). Changed to `simp only … at hh` followed by `exact hh`, leaving the goal
untouched.

8. `minpoly.natDegree_le` renamed its base-ring argument `K` → `A`.

9. `LinearMap.BilinForm.Nondegenerate` is now `SeparatingLeft B ∧ SeparatingRight B`
rather than a directly applicable `∀ x, …`, so `traceForm_nondegenerate K L c` became
`(traceForm_nondegenerate K L).1 c`.

10. `simpa using hx0lo` no longer bridges `1 ≤ a` and `0 < a`; replaced with `omega`.

11. A `dsimp [M]` that now makes no progress (and so errors) was removed — `M` was
already unfolded, so deleting it is semantics-preserving.

12-14. Three of the repairs in 3–5 left the goal reduced to *exactly* the hypothesis
(alpha-equivalent, differing only in the decidability instance that the pretty-printer
hides), which `simp` still would not match. Closed with `exact hz` / `exact hz` and, in
the third case, `exact neg_eq_of_eq_neg hs` — `exact` checks definitional equality, so
the instance mismatch is irrelevant to it.

15. In `linearMap_solution`, pushing the linear map `L` through the scalar action also
needed `map_smul, smul_eq_mul` in the simp set.

## Oqp35 — 3 fixes (two needed a second pass)

1. In `q5CutMatrix_det_of_certificate`, the cast into `ZMod 5` no longer distributes
over the nested `ite`s. Nothing tried would push it through — `apply_ite`,
`push_cast`, `split_ifs`, `Nat.cast_ite` and `Int.cast_ite` all failed to fire (the
matrix is over `ℤ`, so there are two stacked casts). Rather than keep guessing at the
right simp lemma, the fix adds a bridging lemma and discharges it by decision
procedure — both sides are functions of two `Fin 10`s, so the identity is finitely
checkable:

```lean
lemma q5GraphNat_cast : ∀ i j : Fin 10,
    ((q5GraphNat i.1 j.1 : ℤ) : ZMod 5) = q5Graph i j := by decide
```

This is `decide`, not `native_decide`: the latter would add `Lean.ofReduceBool` to the
axiom list and defeat the point of the audit in `STATUS.md`.

2. `Matrix.submatrix_apply` no longer reduces the submatrix application — the
`Matrix.of` wrapper blocks it — leaving `Matrix.submatrix (fun i j ↦ …) ⇑pC ⇑pA i j`
unreduced, so the following `rw [hpA, hpC]` found no match. Unfold the definition
directly instead: `simp only [Matrix.submatrix, Matrix.of_apply]`.

3. `graphPhase_add`: `ring` treats each `∑` as an atom, so it could not see that the
LHS and RHS summands differ only by commutativity (`x i * G i j * d j` versus
`G i j * x i * d j`). Adding AC lemmas to the `simp_rw` did not work (`simp_rw`
requires every rewrite to make progress, and they did not). Instead a `key` lemma
normalises the right-hand summand to the left-hand orientation *before* summing:

```lean
have key : ∀ i j : Fin n, G i j * (x i * d j + d i * x j)
    = x i * G i j * d j + d i * G i j * x j := by intro i j; ring
simp_rw [key, mul_add, add_mul, Finset.sum_add_distrib]
ring
```

## Comparator-side notes (not changes to Atlas code)

Two comparators needed care rather than the obvious one-liner.

**OeisA22030.** `example : Atlas.OeisA22030.a = OeisA22030.a := rfl` fails, even
though the two definitions are *textually identical*: each compiles to its own
recursor, and `rfl` will not reduce one to the other. The comparator proves the
pointwise equality by the same recursion the definition uses. This is a strictly
stronger check than a textual diff — it would fail if the recurrences differed.

**Wotw314.** `largestInducedPathSize` is polymorphic in the vertex type, and stating
the identity unapplied leaves `α` undetermined. The comparator states it applied to a
graph instead.

**OeisA108081.** `xN n = {w | XWord w ∧ w.length = n}` is textually identical on both
sides, but `XWord` is an *inductive predicate* declared separately in each file, and
two `inductive` declarations are distinct constants however identical their
constructors. The comparator proves `Atlas.XWord w ↔ XWord w` by induction in both
directions and derives `xN` equality from it. This is the check that actually matters
for this problem: it establishes that the Atlas file's notion of an X-word is FC's,
which no amount of `rfl` could have shown.
