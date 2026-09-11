import Mathlib
import EvalTools.Markers

/-!
# Written on the Wall II — Conjecture 100

For a simple connected graph `G`,

  `α(G) ≤ ⌈(max_v l(v) + 0.5 · degreeL2Norm(Gᶜ)) / 2⌉`

where `α(G)` is the independence number, `l(v)` is the independence number of
the neighbourhood of `v`, and `degreeL2Norm H` is the square root of the sum of
the squares of the degrees of `H` (WOWII's `length`). Note the complement: the
norm is taken of `Gᶜ`, not `G`.

Vendored from `google-deepmind/formal-conjectures`:

* `conjecture100` is verbatim from
  `FormalConjectures/WrittenOnTheWallII/GraphConjecture100.lean`;
* `degreeL2Norm` from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Degrees.lean`;
* `indepNeighborsCard` from
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Independence.lean`.

`SimpleGraph.indepNum` is Mathlib's own and is used directly, not vendored.
Only the `@[category]` attribute, which is formal-conjectures metadata, is dropped.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace LeanEval.FormalConjectures.Wotw100

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The length of a graph: the square root of the sum of the squares of degrees. -/
noncomputable def degreeL2Norm (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  Real.sqrt (∑ v, (G.degree v : ℝ) ^ 2)

/-- Independence number of the neighbourhood of `v`. -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

/--
WOWII Conjecture 100: for a simple connected graph `G`,
`α(G) ≤ ⌈(max_v l(v) + 0.5 · degreeL2Norm(Gᶜ)) / 2⌉`.
-/
@[eval_problem]
theorem wotw100_conjecture100 [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤ ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
  sorry

end LeanEval.FormalConjectures.Wotw100
