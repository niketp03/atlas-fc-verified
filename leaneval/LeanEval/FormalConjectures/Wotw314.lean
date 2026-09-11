import Mathlib
import EvalTools.Markers

/-!
# Written on the Wall II — Conjecture 314

For every finite simple connected graph `G` with more than one vertex, if `G` is
triangle-free and the size of its largest induced path is at most 4, then `G` is
well totally dominated.

Both the statement and the vocabulary it needs are vendored from
`google-deepmind/formal-conjectures`:

* `IsTotalDominatingSet`, `IsMinimalTotalDominatingSet` and
  `IsWellTotallyDominated` are verbatim from
  `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/WellTotallyDominated.lean`
  (namespace `SimpleGraph`);
* `largestInducedPathSize` and `conjecture314` are verbatim from
  `FormalConjectures/WrittenOnTheWallII/GraphConjecture314.lean`
  (namespace `WrittenOnTheWallII.GraphConjecture314`).

Only the `@[category]` attributes, which are formal-conjectures metadata, are
dropped. A lean-eval workspace depends on Mathlib alone and cannot import
formal-conjectures, so the definitions have to travel with the statement.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

namespace LeanEval.FormalConjectures.Wotw314

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A set `S` is a total dominating set of `G` if every vertex has a neighbor in `S`. -/
def IsTotalDominatingSet (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  ∀ v : α, ∃ w ∈ S, G.Adj v w

/-- A total dominating set `S` is minimal if no proper subset of `S` is also a
total dominating set. -/
def IsMinimalTotalDominatingSet (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  IsTotalDominatingSet G S ∧
  ∀ T : Finset α, T ⊂ S → ¬IsTotalDominatingSet G T

/-- A graph `G` is well totally dominated if every minimal total dominating set
has the same cardinality. -/
def IsWellTotallyDominated (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  ∀ S T : Finset α,
    IsMinimalTotalDominatingSet G S →
    IsMinimalTotalDominatingSet G T →
    S.card = T.card

/-- The size of a largest induced path of `G`, as a natural number.

A subset `s ⊆ V(G)` is an *induced path* when the induced subgraph `G.induce s`
is a tree in which every vertex has degree at most 2 (equivalently: a tree that
is itself a path graph).

**Disambiguation.** This is *not* the `SimpleGraph.path` invariant, which is the
floor of the average distance. -/
noncomputable def largestInducedPathSize (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup { n | ∃ s : Finset α,
              s.card = n ∧
              (G.induce (s : Set α)).IsTree ∧
              ∀ v : (s : Set α), (G.induce (s : Set α)).degree v ≤ 2 }

/--
WOWII Conjecture 314: for every finite simple connected graph `G` with `n > 1`
vertices, if `G` is triangle-free and `largestInducedPathSize G ≤ 4`, then `G`
is well totally dominated.
-/
@[eval_problem]
theorem wotw314_conjecture [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : largestInducedPathSize G ≤ 4) :
    IsWellTotallyDominated G := by
  sorry

end LeanEval.FormalConjectures.Wotw314
