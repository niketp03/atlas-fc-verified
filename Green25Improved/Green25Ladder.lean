/-
Strengthening ladder for the improved Green 25 upper bound, plus the comparator
against the Formal Conjectures statement of `green_25.upper` exactly as published.

This file is a verification artifact, not Formal Conjectures content.
-/

import FormalConjectures.GreensOpenProblems.«25»
import FormalConjectures.GreensOpenProblems.Green25Strong

open Filter Asymptotics

namespace Green25Ladder

/-! ## `exp(x/16)` beats every fixed power of `x` -/

private lemma exp_pow (y : ℝ) (n : ℕ) : Real.exp y ^ n = Real.exp (n * y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← Real.exp_add]
    congr 1
    push_cast
    ring

/-- `(x / (16n))^n ≤ exp(x/16)` for `x ≥ 0`: split `x/16` into `n` equal pieces and
apply `y + 1 ≤ exp y` to each. -/
private lemma pow_le_exp (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (x / (16 * (n : ℝ))) ^ n ≤ Real.exp (x / 16) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h := Real.add_one_le_exp (x / 16)
    simp only [pow_zero]
    linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hy : (0 : ℝ) ≤ x / (16 * (n : ℝ)) := by positivity
  have hle : x / (16 * (n : ℝ)) ≤ Real.exp (x / (16 * (n : ℝ))) := by
    linarith [Real.add_one_le_exp (x / (16 * (n : ℝ)))]
  have h2 : (x / (16 * (n : ℝ))) ^ n ≤ (Real.exp (x / (16 * (n : ℝ)))) ^ n := by
    gcongr
  have h3 : (Real.exp (x / (16 * (n : ℝ)))) ^ n = Real.exp (x / 16) := by
    rw [exp_pow]
    congr 1
    field_simp
  rw [← h3]
  exact h2

/-- Every fixed power of `x` is dominated by `exp(x/16)` up to a constant. -/
private lemma exists_pow_bound (n : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 0 ≤ x → x ^ n ≤ Real.exp (x / 16) * A := by
  refine ⟨(16 * (n : ℝ)) ^ n + 1, by positivity, ?_⟩
  intro x hx
  have hexp1 : (1 : ℝ) ≤ Real.exp (x / 16) := by
    have := Real.add_one_le_exp (x / 16)
    linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero]
    nlinarith
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hA0 : (0 : ℝ) < (16 * (n : ℝ)) ^ n := pow_pos (by linarith) n
  have hpow := pow_le_exp x hx n
  rw [div_pow, div_le_iff₀ hA0] at hpow
  nlinarith [hpow, (Real.exp_pos (x / 16)).le]

/-! ## The new rate is below every polylogarithmic rate -/

/-- `N / exp(√(log N)/16) = o(N / (log N)^k)` for every fixed `k`. -/
theorem strongUpper_isLittleO_polylog (k : ℕ) :
    Green25Atlas.strongUpper =o[atTop] fun N : ℕ => (N : ℝ) / (Real.log N) ^ k := by
  obtain ⟨A, hApos, hA⟩ := exists_pow_bound (2 * k + 1)
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [eventually_ge_atTop (max 2 ⌈Real.exp ((A / c) ^ 2)⌉₊)] with N hN
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) hN
  have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hlkpos : (0 : ℝ) < Real.log (N : ℝ) ^ k := pow_pos hlogpos k
  have hs0 : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.2 hlogpos
  have hs2 : Real.sqrt (Real.log (N : ℝ)) ^ 2 = Real.log (N : ℝ) :=
    Real.sq_sqrt hlogpos.le
  -- `√(log N)` is large
  have hceil : (⌈Real.exp ((A / c) ^ 2)⌉₊ : ℕ) ≤ N := le_trans (le_max_right _ _) hN
  have hexpN : Real.exp ((A / c) ^ 2) ≤ (N : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
  have hlogge : (A / c) ^ 2 ≤ Real.log (N : ℝ) :=
    (Real.le_log_iff_exp_le hNpos).2 hexpN
  have hsge : A / c ≤ Real.sqrt (Real.log (N : ℝ)) := by
    calc A / c = Real.sqrt ((A / c) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ _ := Real.sqrt_le_sqrt hlogge
  have hcs : A ≤ c * Real.sqrt (Real.log (N : ℝ)) := by
    rw [div_le_iff₀ hc] at hsge
    linarith
  -- the key inequality `(log N)^k ≤ c · exp(√(log N)/16)`
  have hkey : Real.log (N : ℝ) ^ k
      ≤ c * Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16) := by
    have h1 := hA (Real.sqrt (Real.log (N : ℝ))) hs0.le
    have h2 : Real.sqrt (Real.log (N : ℝ)) ^ (2 * k + 1)
        ≤ Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16)
          * (c * Real.sqrt (Real.log (N : ℝ))) :=
      h1.trans (mul_le_mul_of_nonneg_left hcs (Real.exp_pos _).le)
    rw [pow_succ] at h2
    have he : Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16)
          * (c * Real.sqrt (Real.log (N : ℝ)))
        = (c * Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16))
          * Real.sqrt (Real.log (N : ℝ)) := by ring
    have h3 : Real.sqrt (Real.log (N : ℝ)) ^ (2 * k) * Real.sqrt (Real.log (N : ℝ))
        ≤ (c * Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16))
          * Real.sqrt (Real.log (N : ℝ)) := by linarith [h2, he]
    have h4 := le_of_mul_le_mul_right h3 hs0
    rwa [pow_mul, hs2] at h4
  -- conclude
  show ‖Green25Atlas.strongUpper N‖ ≤ c * ‖(N : ℝ) / (Real.log (N : ℝ)) ^ k‖
  rw [Green25Atlas.strongUpper, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hNpos.le (Real.exp_pos _).le),
    abs_of_nonneg (div_nonneg hNpos.le hlkpos.le),
    div_le_iff₀ (Real.exp_pos _)]
  have hlkne : Real.log (N : ℝ) ^ k ≠ 0 := hlkpos.ne'
  rw [show c * ((N : ℝ) / Real.log (N : ℝ) ^ k)
        * Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16)
      = (N : ℝ) * (c * Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16))
        / Real.log (N : ℝ) ^ k by field_simp,
    le_div_iff₀ hlkpos]
  exact mul_le_mul_of_nonneg_left hkey hNpos.le

/-- Against the published [ESS89] bound `N / log N`. -/
theorem strongUpper_isLittleO_bestUpper :
    Green25Atlas.strongUpper =o[atTop] Green25.bestUpper := by
  have h := strongUpper_isLittleO_polylog 1
  have he : (fun N : ℕ => (N : ℝ) / (Real.log N) ^ 1) = Green25.bestUpper := by
    funext N
    rw [pow_one, Green25.bestUpper]
  rwa [he] at h

/-- Against `N / (log N)^2`, the rate the Atlas construction reaches at its
published parameter `r = 4 + 4t`. The improvement is therefore strict. -/
theorem strongUpper_isLittleO_logSq :
    Green25Atlas.strongUpper =o[atTop] Green25Atlas.improvedUpper := by
  have h := strongUpper_isLittleO_polylog 2
  have he : (fun N : ℕ => (N : ℝ) / (Real.log N) ^ 2) = Green25Atlas.improvedUpper := by
    funext N
    rw [Green25Atlas.improvedUpper]
  rwa [he] at h

/-! ## Comparator: the Formal Conjectures statement of `green_25.upper`

The statement below is the body of `green_25.upper` in
`FormalConjectures/GreensOpenProblems/25.lean` **verbatim**, with the single
change that `answer(sorry)` is replaced by the function the construction produces.
Note in particular that the third conjunct is Formal Conjectures' own
`¬ ∀ᶠ N, Property25 …`, not the stronger `∀ᶠ N, ¬ Property25 …` that the Atlas
file states, and that `bestUpper` and `Property25` are the Formal Conjectures
definitions, not the copies in the work file.

If this elaborates without `sorry`, the construction answers `green_25.upper`.
-/
theorem fc_green_25_upper_answered :
    let ans := (Green25Atlas.strongAnswer : ℕ → ℕ)
    (∀ᶠ N in atTop, 1 ≤ ans N ∧ ans N ≤ N) ∧
    (fun N => (ans N : ℝ)) =o[atTop] Green25.bestUpper ∧
    ¬ ∀ᶠ N in atTop, Green25.Property25 (ans N) N := by
  intro ans
  refine ⟨Green25Atlas.strongAnswer_size, ?_, ?_⟩
  · exact Green25Atlas.strongAnswer_isBigO.trans_isLittleO
      strongUpper_isLittleO_bestUpper
  · exact Filter.not_eventually.2 Green25Atlas.strongAnswer_not_property.frequently

end Green25Ladder

#print axioms Green25Ladder.strongUpper_isLittleO_polylog
#print axioms Green25Ladder.strongUpper_isLittleO_bestUpper
#print axioms Green25Ladder.strongUpper_isLittleO_logSq
#print axioms Green25Ladder.fc_green_25_upper_answered
