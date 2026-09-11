import Mathlib
import EvalTools.Markers

/-!
# Open Quantum Problem 35 — does an AME(9,10) state exist?

An *absolutely maximally entangled* state AME(n, d) on `n` parties of local
dimension `d` is a normalized state every one of whose reductions onto
`⌊n/2⌋` parties is maximally mixed. Whether an AME(9, 10) state exists is open.

The definitions below are vendored verbatim from
`FormalConjectures/OpenQuantumProblems/35.lean` in
`google-deepmind/formal-conjectures` (namespace `OpenQuantumProblem35`), covering
the chain `Config` → `StateVector` → `IsNormalized` / `permuteState` →
`reducedDensityFirst` → `HasMaximallyMixedFirstReduction` → `IsAME` → `ExistsAME`,
together with the API lemmas the development uses. Only the `@[category]`
attributes, which are formal-conjectures metadata, are dropped.

## A deliberate deviation in statement shape

FC states this as `ame_9_10_open : answer(sorry) ↔ ExistsAME 9 10`. `answer(…)` is
formal-conjectures machinery that does not exist outside that repository, so the
Challenge below is `ExistsAME 9 10` itself — the same instantiation the
hand-written comparator in this repository records for Oqp35, where proving the
right-hand side outright sets the answer to `True`.

*References:*
- Helwig, Cui, Riera, Latorre, Lo (2012)
- Goyeneche, Alsina, Latorre, Riera, Życzkowski (2015)
-/

namespace LeanEval.FormalConjectures.Oqp35

open scoped BigOperators

/-- A computational-basis configuration of $n$ parties with local dimension $d$. -/
abbrev Config (n d : ℕ) := Fin n → Fin d

/-- A state vector in the computational basis, viewed as a finite-dimensional Hilbert space. -/
abbrev StateVector (n d : ℕ) := EuclideanSpace ℂ (Config n d)

/-- Build a state vector from its computational-basis amplitudes. -/
abbrev mkStateVector {n d : ℕ} (ψ : Config n d → ℂ) : StateVector n d :=
  WithLp.toLp 2 ψ

/-- A state vector can be evaluated on a computational-basis configuration to read its amplitude. -/
instance {n d : ℕ} : CoeFun (StateVector n d) (fun _ => Config n d → ℂ) where
  coe ψ := ψ.ofLp

/-- A state built from amplitudes has those amplitudes as its coordinates. -/
@[simp]
lemma mkStateVector_apply {n d : ℕ} (ψ : Config n d → ℂ) (x : Config n d) :
    mkStateVector ψ x = ψ x := rfl

/-- A state vector is normalized if it has $L^2$ norm $1$. -/
def IsNormalized {n d : ℕ} (ψ : StateVector n d) : Prop :=
  ‖ψ‖ = 1

/-- A state is normalized iff its squared $L^2$ norm is $1$. -/
lemma isNormalized_iff_norm_sq_eq_one {n d : ℕ} (ψ : StateVector n d) :
    IsNormalized ψ ↔ ‖ψ‖ ^ 2 = 1 := by
  constructor
  · intro h
    rw [IsNormalized] at h
    calc
      ‖ψ‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [h]
      _ = 1 := by norm_num
  · intro h
    rw [IsNormalized]
    have hsq : ‖ψ‖ ^ 2 = (1 : ℝ) ^ 2 := by
      simpa using h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hnorm | hnorm
    · exact hnorm
    · have hnonneg : 0 ≤ ‖ψ‖ := norm_nonneg ψ
      have : False := by
        linarith
      exact False.elim this

/-- Permute the parties of a configuration. -/
def permuteConfig {n d : ℕ} (π : Equiv.Perm (Fin n)) (x : Config n d) : Config n d :=
  fun i => x (π i)

/-- The identity permutation leaves a configuration unchanged. -/
theorem permuteConfig_refl {n d : ℕ} (x : Config n d) :
    permuteConfig (Equiv.refl (Fin n)) x = x := by
  ext i
  simp [permuteConfig]

/-- Permute the parties of a state vector. -/
def permuteState {n d : ℕ} (π : Equiv.Perm (Fin n)) (ψ : StateVector n d) : StateVector n d :=
  mkStateVector fun x => ψ (permuteConfig π x)

/-- Evaluating a permuted state vector reads the amplitude at the permuted configuration. -/
@[simp]
lemma permuteState_apply {n d : ℕ} (π : Equiv.Perm (Fin n)) (ψ : StateVector n d) (x : Config n d) :
    permuteState π ψ x = ψ (permuteConfig π x) := by
  rw [permuteState, mkStateVector_apply]

/-- The identity permutation leaves a state vector unchanged. -/
theorem permuteState_refl {n d : ℕ} (ψ : StateVector n d) :
    permuteState (Equiv.refl (Fin n)) ψ = ψ := by
  ext x
  simp [permuteState_apply, permuteConfig_refl]

/--
Merge a configuration on the first $m$ parties and a configuration on the remaining $n-m$
parties into a configuration on all $n$ parties.
-/
def combineFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) : Config n d :=
  fun i =>
    if hi : i.1 < m then
      x ⟨i.1, hi⟩
    else
      y ⟨i.1 - m, by
        have him : m ≤ i.1 := Nat.le_of_not_gt hi
        omega⟩

/-- The embedding of the first $m$ indices into $\mathrm{Fin}\, n$. -/
def leftIndex {m n : ℕ} (hm : m ≤ n) (i : Fin m) : Fin n :=
  ⟨i.1, lt_of_lt_of_le i.2 hm⟩

/-- The embedding of the last $n-m$ indices into $\mathrm{Fin}\, n$. -/
def rightIndex {m n : ℕ} (hm : m ≤ n) (i : Fin (n - m)) : Fin n :=
  ⟨m + i.1, by omega⟩

/-- Combining and then restricting to the left block recovers the left input. -/
@[simp]
lemma combineFirst_leftIndex {n d m : ℕ} (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) (i : Fin m) :
    combineFirst (n := n) (d := d) m hm x y (leftIndex hm i) = x i := by
  simp [combineFirst, leftIndex, i.2]

/-- Combining and then restricting to the right block recovers the right input. -/
@[simp]
lemma combineFirst_rightIndex {n d m : ℕ} (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) (i : Fin (n - m)) :
    combineFirst (n := n) (d := d) m hm x y (rightIndex hm i) = y i := by
  have hnot : ¬ m + i.1 < m := by omega
  simp [combineFirst, rightIndex, hnot]

/- ## Reduced density matrices and AME -/

/--
The reduced density matrix obtained by tracing out the last $n-m$ parties.

The subsystem is always the first $m$ parties; different subsystems are handled by first
permuting the parties.
-/
noncomputable def reducedDensityFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n) (ψ : StateVector n d) :
    Matrix (Config m d) (Config m d) ℂ :=
  fun x y =>
    ∑ z : Config (n - m) d,
      ψ (combineFirst (n := n) (d := d) m hm x z) *
        star (ψ (combineFirst (n := n) (d := d) m hm y z))

/-- The maximally mixed state on $m$ parties. -/
noncomputable def maximallyMixed (m d : ℕ) :
    Matrix (Config m d) (Config m d) ℂ :=
  ((Fintype.card (Config m d) : ℂ)⁻¹) •
    (1 : Matrix (Config m d) (Config m d) ℂ)

/-- A state has maximally mixed reduction on the first $m$ parties. -/
def HasMaximallyMixedFirstReduction {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (ψ : StateVector n d) : Prop :=
  reducedDensityFirst (n := n) (d := d) m hm ψ = maximallyMixed m d

/--
A state $\psi$ is absolutely maximally entangled.

Standard AME definitions quantify over all subsets $A \subseteq \mathrm{Fin}\, n$ with
$|A| \le \lfloor n/2 \rfloor$ and require that the reduction on $A$ be maximally mixed.
For pure states it is enough to check subsets of size exactly $\lfloor n/2 \rfloor$; see the
references of Helwig--Cui--Riera--Latorre--Lo (2012) and
Goyeneche--Alsina--Latorre--Riera--Życzkowski (2015). In this file, a subsystem of that size is
encoded by first permuting the chosen parties to the front and then tracing out the remaining
parties.

We also require $\psi$ to be normalized explicitly.
-/
def IsAME {n d : ℕ} (ψ : StateVector n d) : Prop :=
  IsNormalized ψ ∧
    ∀ π : Equiv.Perm (Fin n),
      HasMaximallyMixedFirstReduction (n := n) (d := d)
        (n / 2) (Nat.div_le_self n 2) (permuteState π ψ)

/-- Existence of an $\mathrm{AME}(n,d)$ state. -/
def ExistsAME (n d : ℕ) : Prop :=
  ∃ ψ : StateVector n d, IsAME (n := n) (d := d) ψ

/-- Open benchmark statement: does an $\mathrm{AME}(9,10)$ state exist? -/
@[eval_problem]
theorem oqp35_ame_9_10 : ExistsAME 9 10 := by
  sorry

end LeanEval.FormalConjectures.Oqp35
