/-
A strengthening of the Atlas Green 25 construction.

`complemented_digit_partition Q m r` is stated for **every** `r ≤ m`: it produces a
partition of `[1, Q^m]` into `Q^m / 2^r` parts whose restricted sumsets cover at most
`r * (2Q)^(m-1)` points. The published Atlas file instantiates it at `r = 4 + 4t`,
which is exactly the value that makes the part count equal `B / (log₂ B)^2` — i.e. the
choice is driven by the target `N / (log N)^2`, not by the construction.

The sumset budget is *linear* in `r`, against a denominator of order `Q = 2^(4m)`, so
`r` may be taken all the way up to its structural maximum `r = m = 2^t` at no cost.
That improves the part count from `B / (log₂ B)^2` to `B / 2^(2^t)`, and since
`log₂ B = 4·(2^t)^2` this is `B / 2^(√(log₂ B)/2)`, which beats `B / (log₂ B)^k` for
every fixed `k`.

This file is a verification artifact, not Formal Conjectures content.
-/

import FormalConjectures.GreensOpenProblems.Green25Work

open Asymptotics Filter Finset

namespace Green25Atlas

/-! ## The base-level counterexample with the maximal number of complemented digits -/

private lemma ten_lt_two_pow (n : ℕ) (hn : 6 ≤ n) : 10 * n < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    have hp : (10 : ℕ) ≤ 2 ^ n := by
      calc (10 : ℕ) ≤ 2 ^ 6 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega

/-- The sumset budget at `r = m`: still a vanishing fraction of `Q^m`, with room
to spare. -/
private lemma strong_sumset_bound (m : ℕ) (hm : 32 ≤ m) :
    20 * (m * (2 * 2 ^ (4 * m)) ^ (m - 1)) < (2 ^ (4 * m)) ^ m := by
  have hkey : 20 * m * 2 ^ (m - 1) < 2 ^ (4 * m) := by
    have h1 : 20 * m < 2 ^ (m + 1) := by
      have h := ten_lt_two_pow m (by omega)
      rw [pow_succ]
      omega
    calc 20 * m * 2 ^ (m - 1) < 2 ^ (m + 1) * 2 ^ (m - 1) :=
          Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      _ = 2 ^ (2 * m) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ (4 * m) := Nat.pow_le_pow_right (by omega) (by omega)
  have hexp : (2 ^ (4 * m)) ^ m = (2 ^ (4 * m)) ^ (m - 1) * 2 ^ (4 * m) := by
    rw [← pow_succ]; congr 1; omega
  rw [hexp, mul_pow]
  calc 20 * (m * (2 ^ (m - 1) * (2 ^ (4 * m)) ^ (m - 1)))
      = (20 * m * 2 ^ (m - 1)) * (2 ^ (4 * m)) ^ (m - 1) := by ring
    _ < 2 ^ (4 * m) * (2 ^ (4 * m)) ^ (m - 1) :=
        Nat.mul_lt_mul_of_pos_right hkey (by positivity)
    _ = (2 ^ (4 * m)) ^ (m - 1) * 2 ^ (4 * m) := by ring

/-- The `r = m` instance of `complemented_digit_partition`. -/
lemma digit_partition_strong (t : ℕ) (ht : 5 ≤ t) :
    ∃ P : Finpartition (Icc 1 (2 ^ (4 * (2 ^ t) ^ 2))),
      #P.parts = 2 ^ (4 * (2 ^ t) ^ 2) / 2 ^ (2 ^ t) ∧
      20 * #(P.parts.biUnion Finset.restrictedSumset) <
        2 ^ (4 * (2 ^ t) ^ 2) := by
  have hm32 : (32 : ℕ) ≤ 2 ^ t := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
  have hQ : 2 ≤ 2 ^ (4 * 2 ^ t) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (4 * 2 ^ t) := Nat.pow_le_pow_right (by omega) (by omega)
  have heven : 2 ∣ 2 ^ (4 * 2 ^ t) := dvd_pow_self 2 (by omega)
  have hN : (2 ^ (4 * 2 ^ t)) ^ (2 ^ t) = 2 ^ (4 * (2 ^ t) ^ 2) := by
    rw [← pow_mul]; congr 1; ring
  have hpart := complemented_digit_partition (2 ^ (4 * 2 ^ t)) (2 ^ t) (2 ^ t)
    hQ heven le_rfl
  rw [hN] at hpart
  obtain ⟨P, hcard, hsum⟩ := hpart
  refine ⟨P, hcard, ?_⟩
  calc 20 * #(P.parts.biUnion Finset.restrictedSumset)
      ≤ 20 * (2 ^ t * (2 * 2 ^ (4 * 2 ^ t)) ^ (2 ^ t - 1)) :=
        Nat.mul_le_mul_left 20 hsum
    _ < (2 ^ (4 * 2 ^ t)) ^ (2 ^ t) := strong_sumset_bound (2 ^ t) hm32
    _ = 2 ^ (4 * (2 ^ t) ^ 2) := hN

/-! ## Tiling, generalised over the base partition

`tiled_digit_partition` hard-codes `digit_partition` as its base, but the tiling
argument only ever uses the part count and the sumset bound. -/

lemma tiled_of_base (B N c : ℕ) (hB : 0 < B) (hN : B ≤ N)
    (hbase : ∃ P₀ : Finpartition (Icc 1 B),
      #P₀.parts = c ∧ 20 * #(P₀.parts.biUnion Finset.restrictedSumset) < B) :
    ∃ P : Finpartition (Icc 1 N),
      #P.parts ≤ (N / B + 1) * c ∧
      10 * #(P.parts.biUnion Finset.restrictedSumset) < N := by
  obtain ⟨P₀, hPcard, hPsum⟩ := hbase
  let q := N / B + 1
  have hNB : N ≤ q * B := by
    calc
      N = N % B + B * (N / B) := (Nat.mod_add_div N B).symm
      _ = N % B + (N / B) * B := by ac_rfl
      _ ≤ B + (N / B) * B :=
        Nat.add_le_add_right (Nat.le_of_lt (Nat.mod_lt N hB)) _
      _ = q * B := by simp [q]; ring
  have hsub : Icc 1 N ⊆ Icc 1 (q * B) := by
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, hx.2.trans hNB⟩
  let R := repeatPartition25 q hB P₀
  obtain ⟨P, hPparts, hPsubset⟩ := restrict_partition25 R hsub
  refine ⟨P, ?_, ?_⟩
  · calc
      #P.parts ≤ #R.parts := hPparts
      _ ≤ q * #P₀.parts := repeatPartition25_card_le q hB P₀
      _ = (N / B + 1) * c := by rw [hPcard]
  · have hsum : #(P.parts.biUnion Finset.restrictedSumset) ≤
        q * #(P₀.parts.biUnion Finset.restrictedSumset) :=
      (Finset.card_le_card hPsubset).trans (repeatPartition25_sum_le q hB P₀)
    have hq : 0 < q := by simp [q]
    have hqsmall : q * (20 * #(P₀.parts.biUnion Finset.restrictedSumset)) < q * B :=
      Nat.mul_lt_mul_of_pos_left hPsum hq
    have hqB : q * B ≤ N + B := by
      simp only [q, Nat.add_mul]
      simpa using Nat.add_le_add_right (Nat.div_mul_le_self N B) B
    calc
      10 * #(P.parts.biUnion Finset.restrictedSumset) ≤
          10 * (q * #(P₀.parts.biUnion Finset.restrictedSumset)) :=
        Nat.mul_le_mul_left 10 hsum
      _ < N := by nlinarith

/-! ## The selected partition at the strong parameter -/

/-- Part count of the strong base partition at level `t`. -/
def strongCount (t : ℕ) : ℕ := scale25 t / 2 ^ (2 ^ t)

private lemma strongCount_mul (t : ℕ) : strongCount t * 2 ^ (2 ^ t) = scale25 t := by
  have h1 : (1 : ℕ) ≤ 2 ^ t := Nat.one_le_pow _ _ (by omega)
  have hle : 2 ^ t ≤ 4 * (2 ^ t) ^ 2 := by nlinarith [h1, sq_nonneg (2 ^ t)]
  rw [strongCount, scale25, Nat.pow_div hle (by omega), ← pow_add,
    Nat.sub_add_cancel hle]

lemma strong_tiled (N : ℕ) (h : 5 ≤ level25 N ∧ scale25 (level25 N) ≤ N) :
    ∃ P : Finpartition (Icc 1 N),
      #P.parts ≤ (N / scale25 (level25 N) + 1) * strongCount (level25 N) ∧
      10 * #(P.parts.biUnion Finset.restrictedSumset) < N := by
  refine tiled_of_base (scale25 (level25 N)) N (strongCount (level25 N)) ?_ h.2 ?_
  · rw [scale25]; positivity
  · exact digit_partition_strong (level25 N) h.1

noncomputable def strongPartition25 (N : ℕ) : Finpartition (Icc 1 N) :=
  if h : 5 ≤ level25 N ∧ scale25 (level25 N) ≤ N then
    Classical.choose (strong_tiled N h)
  else fallbackPartition25 N

lemma strongPartition25_spec (N : ℕ)
    (h : 5 ≤ level25 N ∧ scale25 (level25 N) ≤ N) :
    #(strongPartition25 N).parts ≤
        (N / scale25 (level25 N) + 1) * strongCount (level25 N) ∧
      10 * #((strongPartition25 N).parts.biUnion Finset.restrictedSumset) < N := by
  rw [strongPartition25, dif_pos h]
  exact Classical.choose_spec (strong_tiled N h)

/-! ## The counting bound, in ℕ -/

lemma strongPartition25_count (N : ℕ) (hN : 4 ^ 6 ≤ Nat.log 2 N) :
    #(strongPartition25 N).parts * 2 ^ (2 ^ level25 N) ≤ 2 * N := by
  have hg := level25_good N hN
  have hspec := strongPartition25_spec N hg
  have hqB : (N / scale25 (level25 N) + 1) * scale25 (level25 N) ≤ 2 * N := by
    have hBN := hg.2
    calc
      (N / scale25 (level25 N) + 1) * scale25 (level25 N)
          ≤ N + scale25 (level25 N) := by
        rw [Nat.add_mul]
        simpa using Nat.add_le_add_right
          (Nat.div_mul_le_self N (scale25 (level25 N))) (scale25 (level25 N))
      _ ≤ 2 * N := by omega
  calc
    #(strongPartition25 N).parts * 2 ^ (2 ^ level25 N)
        ≤ ((N / scale25 (level25 N) + 1) * strongCount (level25 N))
            * 2 ^ (2 ^ level25 N) :=
      Nat.mul_le_mul_right _ hspec.1
    _ = (N / scale25 (level25 N) + 1) * scale25 (level25 N) := by
      rw [mul_assoc, strongCount_mul]
    _ ≤ 2 * N := hqB

/-- The level is large: `log₂ N < 16 · (2^t)^2`, so `2^t > √(log₂ N)/4`. -/
lemma log2_lt_level (N : ℕ) (hN : 4 ^ 6 ≤ Nat.log 2 N) :
    Nat.log 2 N < 16 * (2 ^ level25 N) ^ 2 := by
  have hu : 6 ≤ Nat.log 4 (Nat.log 2 N) := Nat.le_log_of_pow_le (by omega) hN
  have htu : level25 N + 1 = Nat.log 4 (Nat.log 2 N) := by
    rw [level25]; omega
  have h4t : (4 : ℕ) ^ level25 N = (2 ^ level25 N) ^ 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    omega
  have hh := Nat.lt_pow_succ_log_self (by omega : 1 < 4) (Nat.log 2 N)
  rw [← htu, pow_succ] at hh
  calc Nat.log 2 N < 4 ^ (level25 N + 1) * 4 := hh
    _ = 16 * (2 ^ level25 N) ^ 2 := by rw [pow_succ, h4t]; ring

/-! ## The analytic step -/

private lemma log_le_two_mul_log2 (N : ℕ) (hN : 1 < N) :
    Real.log (N : ℝ) ≤ 2 * ((Nat.log 2 N : ℕ) : ℝ) := by
  have hpow := Nat.lt_pow_succ_log_self (by omega : 1 < 2) N
  have hcast : (N : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 N + 1) := by
    exact_mod_cast (Nat.le_of_lt hpow)
  have hh := Real.strictMonoOn_log.monotoneOn
    (show (N : ℝ) ∈ Set.Ioi 0 by
      change (0 : ℝ) < N
      exact_mod_cast (Nat.zero_lt_of_lt hN))
    (show (2 : ℝ) ^ (Nat.log 2 N + 1) ∈ Set.Ioi 0 by
      change (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 N + 1)
      positivity) hcast
  rw [Real.log_pow] at hh
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have h2N : (2 : ℕ) ^ 1 ≤ N := by rw [pow_one]; omega
  have hLone : (1 : ℝ) ≤ ((Nat.log 2 N : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_log_of_pow_le (by omega) h2N
  calc
    Real.log (N : ℝ) ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.log 2 := hh
    _ ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hlog2 (by positivity)
    _ ≤ 2 * ((Nat.log 2 N : ℕ) : ℝ) := by push_cast; nlinarith

/-- If `log₂ N < 16 m²` then `exp(√(log N)/16) ≤ 2^m`. The slack is real:
`√(log N) ≤ 6m` and `6/16 = 0.375 < log 2`. -/
private lemma exp_sqrt_log_le (N m : ℕ) (hN : 1 < N)
    (hm : Nat.log 2 N < 16 * m ^ 2) :
    Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16) ≤ (2 : ℝ) ^ m := by
  have hlogle := log_le_two_mul_log2 N hN
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hmR : ((Nat.log 2 N : ℕ) : ℝ) < 16 * (m : ℝ) ^ 2 := by exact_mod_cast hm
  have hsqrt : Real.sqrt (Real.log (N : ℝ)) ≤ 6 * (m : ℝ) := by
    have hnn : (0 : ℝ) ≤ 6 * (m : ℝ) := by positivity
    calc Real.sqrt (Real.log (N : ℝ)) ≤ Real.sqrt ((6 * (m : ℝ)) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 6 * (m : ℝ) := Real.sqrt_sq hnn
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hstep : Real.sqrt (Real.log (N : ℝ)) / 16 ≤ (m : ℝ) * Real.log 2 := by
    have hpos : (0 : ℝ) < Real.log 2 - 0.375 := by linarith
    have hprod : (0 : ℝ) ≤ (m : ℝ) * (Real.log 2 - 0.375) := mul_nonneg hmnn hpos.le
    nlinarith
  have hexpM : Real.exp ((m : ℝ) * Real.log 2) = (2 : ℝ) ^ m := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  calc Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16)
      ≤ Real.exp ((m : ℝ) * Real.log 2) := Real.exp_le_exp.2 hstep
    _ = (2 : ℝ) ^ m := hexpM

/-! ## The improved rate -/

/-- The improved upper bound `N / exp(√(log N)/16)`: below `N / (log N)^k` for
every fixed `k`, hence below the whole polylogarithmic scale `bestUpper` lives on. -/
noncomputable def strongUpper (N : ℕ) : ℝ :=
  (N : ℝ) / Real.exp (Real.sqrt (Real.log N) / 16)

/-- The explicit partition size the construction produces. -/
noncomputable def strongAnswer (N : ℕ) : ℕ := #(strongPartition25 N).parts

lemma strongAnswer_size : ∀ᶠ N in atTop, 1 ≤ strongAnswer N ∧ strongAnswer N ≤ N := by
  filter_upwards [eventually_ge_atTop (2 ^ (4 ^ 6))] with N hN
  have hN1 : 1 ≤ N := by
    calc
      1 ≤ 2 ^ (4 ^ 6) := one_le_pow₀ (by omega)
      _ ≤ N := hN
  constructor
  · show 1 ≤ #(strongPartition25 N).parts
    exact ((strongPartition25 N).parts_nonempty (by simp [hN1])).card_pos
  · show #(strongPartition25 N).parts ≤ N
    simpa [Nat.card_Icc] using (strongPartition25 N).card_parts_le_card

lemma strongAnswer_isBigO :
    (fun N => (strongAnswer N : ℝ)) =O[atTop] strongUpper := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, ?_⟩
  filter_upwards [eventually_ge_atTop (2 ^ (4 ^ 6))] with N hN
  have hL : 4 ^ 6 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) hN
  have hN1 : 1 < N := by
    have hbase : 2 ^ (4 ^ 6) ≤ N := hN
    have hpowbig : 1 < 2 ^ (4 ^ 6) := Nat.one_lt_two_pow (by norm_num)
    omega
  have hcount := strongPartition25_count N hL
  have hlevel := log2_lt_level N hL
  have hexple := exp_sqrt_log_le N (2 ^ level25 N) hN1 hlevel
  have hansnn : (0 : ℝ) ≤ (strongAnswer N : ℝ) := by positivity
  have hansR : (strongAnswer N : ℝ) * (2 : ℝ) ^ (2 ^ level25 N) ≤ 2 * (N : ℝ) := by
    exact_mod_cast hcount
  rw [Real.norm_eq_abs, abs_of_nonneg hansnn, strongUpper, Real.norm_eq_abs,
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (N : ℝ) / Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16))]
  calc
    (strongAnswer N : ℝ)
        = ((strongAnswer N : ℝ) * Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16))
            / Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16) := by
          field_simp
    _ ≤ ((strongAnswer N : ℝ) * (2 : ℝ) ^ (2 ^ level25 N))
            / Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16) := by
          gcongr
    _ ≤ (2 * (N : ℝ)) / Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16) := by
          gcongr
    _ = 2 * ((N : ℝ) / Real.exp (Real.sqrt (Real.log (N : ℝ)) / 16)) := by ring

lemma strongAnswer_not_property :
    ∀ᶠ N in atTop, ¬ Property25 (strongAnswer N) N := by
  filter_upwards [eventually_ge_atTop (2 ^ (4 ^ 6))] with N hN
  have hL : 4 ^ 6 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) hN
  have hg := level25_good N hL
  intro hprop
  have hsmall := (strongPartition25_spec N hg).2
  exact (not_le_of_gt hsmall) (hprop.2.2 (strongPartition25 N) rfl)

/--
The improved counterexample: there is a partition size
`k(N) = O(N / exp(√(log N)/16))` for which `Property25` fails for every large `N`.

This is the Atlas construction run at the largest admissible number of complemented
digits, rather than at the number that happens to produce `N/(log N)^2`.
-/
@[category research solved, AMS 5 11]
theorem green_25.variants.upper_exp_sqrt_log :
    ∃ k : ℕ → ℕ,
      (∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N) ∧
      (fun N => (k N : ℝ)) =O[atTop] strongUpper ∧
      ∀ᶠ N in atTop, ¬ Property25 (k N) N :=
  ⟨strongAnswer, strongAnswer_size, strongAnswer_isBigO, strongAnswer_not_property⟩

end Green25Atlas

#print axioms Green25Atlas.strongAnswer_isBigO
#print axioms Green25Atlas.green_25.variants.upper_exp_sqrt_log
