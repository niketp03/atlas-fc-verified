/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import FormalConjectures.GreensOpenProblems.«25»

/-!
# Green's Open Problem 25 — lowering the `N / log N` upper bound

**Problem:** `Green25.green_25.upper` in
[`FormalConjectures/GreensOpenProblems/25.lean`](https://github.com/google-deepmind/formal-conjectures/blob/990d209a1ffbe75e59e11267242675931f524824/FormalConjectures/GreensOpenProblems/25.lean).

**Solution:** `AtlasFCSolutions.Green25.green_25.upper` at the bottom of this file.

The problem file is imported, and every definition the statement mentions is formal-conjectures'
own (reached through `open Green25`); this file declares no copy of any of them. The final
theorem has the same name as the formal-conjectures theorem and repeats its statement.

The answer is `strongAnswer N = O(N / exp(√(log N) / 16))`, which is `o(N / (log N)^k)` for
every fixed `k` (`strongAnswer_rate`). formal-conjectures' statement only asks for `o(N / log N)`.

The digit-partition machinery is from `Atlas/FC/Green25_upper_solution.lean` in
[facebookresearch/atlas-lean](https://github.com/facebookresearch/atlas-lean) (`prepare-atlas-v2`,
`223d8bc`), with its local copies of formal-conjectures' definitions removed and small repairs for
Mathlib drift. The Atlas file used it at a parameter giving `N / (log N)²` parts; here it is used
at the largest admissible parameter instead. See `NOTES.md`.
-/

open Asymptotics Filter Finset

-- formal-conjectures' definitions. Opened before `namespace` so that the name refers to
-- formal-conjectures' namespace and not to `AtlasFCSolutions.Green25`.
open Green25

namespace AtlasFCSolutions.Green25

def complementKey (Q a : ℕ) : ℕ := min a (Q - 1 - a)

private lemma complementKey_eq_iff (Q a b : ℕ) (ha : a < Q) (hb : b < Q)
    (heven : 2 ∣ Q) :
    complementKey Q a = complementKey Q b ↔ b = a ∨ b = Q - 1 - a := by
  obtain ⟨k, rfl⟩ := heven
  simp only [complementKey, min_def]
  split_ifs <;> omega

private lemma ne_complement (Q a : ℕ) (ha : a < Q) (heven : 2 ∣ Q) :
    a ≠ Q - 1 - a := by
  obtain ⟨k, rfl⟩ := heven
  omega

private def digitVector (Q m x : ℕ) [NeZero (Q ^ m)] : Fin m → Fin Q :=
  finFunctionFinEquiv.symm (Fin.ofNat (Q ^ m) (x - 1))

private def encodeVector {Q m : ℕ} (v : Fin m → Fin Q) : ℕ :=
  (finFunctionFinEquiv v : ℕ) + 1

private lemma digitVector_encode (Q m : ℕ) [NeZero (Q ^ m)] (v : Fin m → Fin Q) :
    digitVector Q m (encodeVector v) = v := by
  apply finFunctionFinEquiv.injective
  apply Fin.ext
  have h := (finFunctionFinEquiv v).isLt
  simp only [digitVector, encodeVector, Equiv.apply_symm_apply, Fin.ofNat,
    Nat.add_sub_cancel]
  exact Nat.mod_eq_of_lt h

private lemma encodeVector_mem (Q m : ℕ) (v : Fin m → Fin Q) :
    encodeVector v ∈ Icc 1 (Q ^ m) := by
  simp only [Finset.mem_Icc, encodeVector]
  constructor <;> omega

private lemma encode_digitVector (Q m x : ℕ) [NeZero (Q ^ m)]
    (hx : x ∈ Icc 1 (Q ^ m)) : encodeVector (digitVector Q m x) = x := by
  simp only [Finset.mem_Icc] at hx
  simp only [encodeVector, digitVector, Equiv.apply_symm_apply, Fin.ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

private def vectorKey (Q m r : ℕ) [NeZero (Q ^ m)] (x : ℕ) : Fin m → ℕ := fun i =>
  if i.1 < r then complementKey Q (digitVector Q m x i) else digitVector Q m x i

private def flipVector (Q r : ℕ) {m : ℕ} (v : Fin m → Fin Q)
    (b : Fin r → Bool) : Fin m → Fin Q := fun i =>
  if h : i.1 < r then
    if b ⟨i, h⟩ then ⟨Q - 1 - v i, by have := (v i).isLt; omega⟩ else v i
  else v i

lemma complemented_digit_partition (Q m r : ℕ) (hQ : 2 ≤ Q) (heven : 2 ∣ Q)
    (hr : r ≤ m) :
    ∃ P : Finpartition (Icc 1 (Q ^ m)),
      #P.parts = Q ^ m / 2 ^ r ∧
      #(P.parts.biUnion Finset.restrictedSumset) ≤ r * (2 * Q) ^ (m - 1) := by
  letI : NeZero (Q ^ m) := ⟨pow_ne_zero _ (by omega)⟩
  let s : Setoid ℕ := Setoid.ker (vectorKey Q m r)
  letI : DecidableRel s.r := Classical.decRel _
  let P : Finpartition (Icc 1 (Q ^ m)) := Finpartition.ofSetSetoid s _
  have hcardpart : ∀ p ∈ P.parts, #p = 2 ^ r := by
    intro p hp
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hp
    have haI : a ∈ Icc 1 (Q ^ m) := P.subset hp ha
    rw [← P.part_eq_of_mem hp ha]
    let v := digitVector Q m a
    let f : (Fin r → Bool) → ℕ := fun b => encodeVector (flipVector Q r v b)
    have hfmem : ∀ b : Fin r → Bool, f b ∈ P.part a := by
      intro b
      rw [show P = Finpartition.ofSetSetoid s (Icc 1 (Q ^ m)) by rfl]
      rw [Finpartition.mem_part_ofSetSetoid_iff_rel]
      exact ⟨haI, encodeVector_mem Q m (flipVector Q r v b), by
        change (Setoid.ker (vectorKey Q m r)) a (f b)
        rw [Setoid.ker_def]
        funext i
        change (if i.1 < r then complementKey Q (digitVector Q m a i)
          else digitVector Q m a i) =
          (if i.1 < r then complementKey Q (digitVector Q m (encodeVector (flipVector Q r v b)) i)
          else digitVector Q m (encodeVector (flipVector Q r v b)) i)
        rw [digitVector_encode Q m]
        simp only [v]
        by_cases hi : i.1 < r
        · by_cases hb : b ⟨i, hi⟩ = true
          · have hc : complementKey Q (digitVector Q m a i) =
                complementKey Q (Q - 1 - digitVector Q m a i) :=
              (complementKey_eq_iff Q _ _ (by omega) (by omega) heven).2 (Or.inr rfl)
            simpa [flipVector, hi, hb] using hc
          · simp [flipVector, hi, hb]
        · simp [hi, flipVector]
        ⟩
    have hfinj : Function.Injective f := by
      intro b c hbc
      have hv : flipVector Q r v b = flipVector Q r v c := by
        apply finFunctionFinEquiv.injective
        apply Fin.ext
        have hbc' : (finFunctionFinEquiv (flipVector Q r v b) : ℕ) + 1
            = (finFunctionFinEquiv (flipVector Q r v c) : ℕ) + 1 := hbc
        omega
      funext j
      let i : Fin m := ⟨j, lt_of_lt_of_le j.isLt hr⟩
      have hij : i.1 < r := j.isLt
      have hh := congrFun hv i
      have hhval := congrArg Fin.val hh
      have hji : (⟨i, hij⟩ : Fin r) = j := Fin.ext rfl
      simp only [flipVector, dif_pos hij, hji] at hhval
      have hn := ne_complement Q (v i) (v i).isLt heven
      cases hb : b j <;> cases hc : c j
      · rfl
      · exfalso
        simp [hb, hc] at hhval
        apply hn
        omega
      · exfalso
        simp [hb, hc] at hhval
        apply hn
        omega
      · rfl
    have hc := Finset.card_bij (fun b (_ : b ∈ (Finset.univ : Finset (Fin r → Bool))) => f b)
      (fun b _ => hfmem b)
      (fun b _ c _ h => hfinj h)
      (fun x hx => by
        rw [show P = Finpartition.ofSetSetoid s (Icc 1 (Q ^ m)) by rfl] at hx
        rw [Finpartition.mem_part_ofSetSetoid_iff_rel] at hx
        let w := digitVector Q m x
        let b : Fin r → Bool := fun j => decide (w ⟨j, lt_of_lt_of_le j.isLt hr⟩ ≠
          v ⟨j, lt_of_lt_of_le j.isLt hr⟩)
        refine ⟨b, Finset.mem_univ _, ?_⟩
        change f b = x
        rw [← encode_digitVector Q m x hx.2.1]
        change encodeVector (flipVector Q r v b) = encodeVector (digitVector Q m x)
        apply congrArg encodeVector
        ext i
        by_cases hi : i.1 < r
        · have hkey := congrFun hx.2.2 i
          simp only [s, Setoid.ker_def, vectorKey, hi, ↓reduceIte] at hkey
          have hkey' : complementKey Q (v i) = complementKey Q (w i) := by
            simpa [v, w] using hkey
          have hor := (complementKey_eq_iff Q _ _ (v i).isLt (w i).isLt heven).1 hkey'
          change (flipVector Q r v b i).1 = (w i).1
          by_cases heq : w i = v i
          · simpa [flipVector, hi, b, heq]
          · rcases hor with hor | hor
            · exact (heq (Fin.ext hor)).elim
            · simpa [flipVector, hi, b, heq] using hor.symm
        · have hkey := congrFun hx.2.2 i
          simp only [s, Setoid.ker_def, vectorKey, hi, ↓reduceIte] at hkey
          change (flipVector Q r v b i).1 = (w i).1
          simpa [flipVector, hi, v, w] using hkey)
    simpa [Fintype.card_fun] using hc.symm
  refine ⟨P, ?_, ?_⟩
  · have hs := P.sum_card_parts
    have heq : #P.parts * 2 ^ r = Q ^ m := by
      calc
        #P.parts * 2 ^ r = ∑ p ∈ P.parts, 2 ^ r := by simp
        _ = ∑ p ∈ P.parts, #p := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hcardpart p hp]
        _ = #(Icc 1 (Q ^ m)) := hs
        _ = Q ^ m := by simp [Nat.card_Icc]
    exact (Nat.div_eq_of_eq_mul_left (by positivity) heq.symm).symm
  · by_cases hr0 : r = 0
    · subst r
      simp only [zero_mul, Nat.le_zero]
      rw [Finset.card_eq_zero]
      ext z
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨p, hp, hz⟩
        rw [Finset.restrictedSumset] at hz
        obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hz
        rw [Finset.mem_offDiag] at hxy
        have hc := hcardpart p hp
        rw [pow_zero] at hc
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
        simp_all
      · simp
    · have hm0 : m ≠ 0 := by omega
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      let C := Fin r × (Fin n → Fin (2 * Q))
      let decode : C → ℕ := fun c =>
        let j : Fin (n + 1) := ⟨c.1.1, lt_of_lt_of_le c.1.2 hr⟩
        let d : Fin (n + 1) → Fin (2 * Q) :=
          Fin.insertNth j ⟨Q - 1, by omega⟩ c.2
        2 + ∑ i, (d i : ℕ) * Q ^ (i : ℕ)
      have hsubset : P.parts.biUnion Finset.restrictedSumset ⊆
          (Finset.univ : Finset C).image decode := by
        intro z hz
        rw [Finset.mem_biUnion] at hz
        obtain ⟨p, hp, hz⟩ := hz
        rw [Finset.restrictedSumset] at hz
        obtain ⟨xy, hxy, hsum⟩ := Finset.mem_image.mp hz
        rw [Finset.mem_offDiag] at hxy
        let x := xy.1
        let y := xy.2
        have hx : x ∈ p := hxy.1
        have hy : y ∈ p := hxy.2.1
        have hne : x ≠ y := hxy.2.2
        have hxI : x ∈ Icc 1 (Q ^ (n + 1)) := P.subset hp hx
        have hyI : y ∈ Icc 1 (Q ^ (n + 1)) := P.subset hp hy
        have hyPart : y ∈ P.part x := by
          rw [P.part_eq_of_mem hp hx]
          exact hy
        have hrel : vectorKey Q (n + 1) r x = vectorKey Q (n + 1) r y := by
          rw [show P = Finpartition.ofSetSetoid s (Icc 1 (Q ^ (n + 1))) by rfl] at hyPart
          rw [Finpartition.mem_part_ofSetSetoid_iff_rel] at hyPart
          exact hyPart.2.2
        let vx := digitVector Q (n + 1) x
        let vy := digitVector Q (n + 1) y
        have hvne : vx ≠ vy := by
          intro hv
          apply hne
          rw [← encode_digitVector Q (n + 1) x hxI,
            ← encode_digitVector Q (n + 1) y hyI]
          change encodeVector vx = encodeVector vy
          rw [hv]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hvne
        have hir : i.1 < r := by
          by_contra hir
          have hk := congrFun hrel i
          simp only [vectorKey, hir, ↓reduceIte] at hk
          exact hi (Fin.ext hk)
        have hk := congrFun hrel i
        simp only [vectorKey, hir, ↓reduceIte] at hk
        have hk' : complementKey Q (vx i) = complementKey Q (vy i) := by
          simpa [vx, vy] using hk
        have hor := (complementKey_eq_iff Q _ _ (vx i).isLt (vy i).isLt heven).1 hk'
        have hcomp : (vy i : ℕ) = Q - 1 - (vx i : ℕ) := by
          rcases hor with hor | hor
          · exact (hi (Fin.ext hor.symm)).elim
          · exact hor
        let j : Fin r := ⟨i.1, hir⟩
        let jm : Fin (n + 1) := ⟨j.1, lt_of_lt_of_le j.2 hr⟩
        have hjm : jm = i := Fin.ext rfl
        let d : Fin (n + 1) → Fin (2 * Q) := fun k =>
          ⟨(vx k : ℕ) + (vy k : ℕ), by
            have hxlt := (vx k).isLt
            have hylt := (vy k).isLt
            omega⟩
        have hdjm : d jm = (⟨Q - 1, by omega⟩ : Fin (2 * Q)) := by
          apply Fin.ext
          simp only [d, hjm]
          omega
        let c : C := (j, Fin.removeNth jm d)
        refine Finset.mem_image.mpr ⟨c, Finset.mem_univ _, ?_⟩
        have hrecon : Fin.insertNth jm (⟨Q - 1, by omega⟩ : Fin (2 * Q))
            (Fin.removeNth jm d) = d := by
          rw [Fin.insertNth_removeNth]
          rw [show (⟨Q - 1, by omega⟩ : Fin (2 * Q)) = d jm from hdjm.symm]
          simp
        change 2 + ∑ k, ((Fin.insertNth jm (⟨Q - 1, by omega⟩ : Fin (2 * Q))
          (Fin.removeNth jm d)) k : ℕ) * Q ^ (k : ℕ) = z
        rw [hrecon]
        change x + y = z at hsum
        rw [← hsum]
        rw [← encode_digitVector Q (n + 1) x hxI,
          ← encode_digitVector Q (n + 1) y hyI]
        simp only [encodeVector, finFunctionFinEquiv_apply, d, vx, vy,
          Nat.add_mul, Finset.sum_add_distrib]
        omega
      calc
        #(P.parts.biUnion Finset.restrictedSumset) ≤
            #((Finset.univ : Finset C).image decode) := Finset.card_le_card hsubset
        _ ≤ #(Finset.univ : Finset C) := Finset.card_image_le
        _ = r * (2 * Q) ^ ((n + 1) - 1) := by
          simp [C, Fintype.card_fun]

private def shift25 (a : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.image (a + ·)

private lemma shift25_injective (a : ℕ) : Function.Injective (shift25 a) := by
  intro s t h
  ext x
  have hmem := Finset.ext_iff.mp h (a + x)
  simpa [shift25] using hmem

private def shiftPartition25 {s : Finset ℕ} (a : ℕ) (P : Finpartition s) :
    Finpartition (shift25 a s) where
  parts := P.parts.image (shift25 a)
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, Finset.mem_image]
    rintro A ⟨p, hp, rfl⟩ B ⟨q, hq, rfl⟩ hAB
    rw [Function.onFun, id_eq, Finset.disjoint_left]
    intro z hzp hzq
    change z ∈ shift25 a p at hzp
    change z ∈ shift25 a q at hzq
    rw [shift25, Finset.mem_image] at hzp hzq
    obtain ⟨x, hx, rfl⟩ := hzp
    obtain ⟨y, hy, hxy⟩ := hzq
    have hxy' : x = y := by omega
    subst y
    have hd := P.disjoint hp hq (fun h => hAB (congrArg (shift25 a) h))
    change Disjoint p q at hd
    rw [Finset.disjoint_left] at hd
    exact hd hx hy
  sup_parts := by
    ext x
    simp only [Finset.mem_sup, Finset.mem_image]
    constructor
    · rintro ⟨u, ⟨p, hp, hpu⟩, hu⟩
      subst u
      change x ∈ shift25 a p at hu
      rw [shift25, Finset.mem_image] at hu
      obtain ⟨y, hy, rfl⟩ := hu
      rw [shift25, Finset.mem_image]
      refine ⟨y, ?_, rfl⟩
      rw [← P.sup_parts, Finset.mem_sup]
      exact ⟨p, hp, hy⟩
    · change x ∈ s.image (a + ·) → _
      rw [Finset.mem_image]
      rintro ⟨y, hy, rfl⟩
      rw [← P.sup_parts, Finset.mem_sup] at hy
      obtain ⟨p, hp, hyp⟩ := hy
      refine ⟨shift25 a p, ⟨p, hp, rfl⟩, ?_⟩
      change a + y ∈ shift25 a p
      exact Finset.mem_image.mpr ⟨y, hyp, rfl⟩
  bot_notMem := by
    rw [Finset.mem_image]
    rintro ⟨p, hp, hzero⟩
    have hpzero : p = ∅ := by
      ext x
      simp only [Finset.notMem_empty, iff_false]
      intro hx
      have hm : a + x ∈ shift25 a p := by
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      rw [hzero] at hm
      exact (Finset.notMem_empty _ hm).elim
    subst p
    exact P.bot_notMem hp

private lemma shiftPartition25_card {s : Finset ℕ} (a : ℕ) (P : Finpartition s) :
    #(shiftPartition25 a P).parts = #P.parts := by
  exact Finset.card_image_iff.mpr fun _ _ _ _ h => shift25_injective a h

private def repeatPartition25 {B : ℕ} (q : ℕ) (hB : 0 < B)
    (P : Finpartition (Icc 1 B)) : Finpartition (Icc 1 (q * B)) := by
  let block : Fin q → Finset ℕ := fun i => shift25 (i.1 * B) (Icc 1 B)
  let part : (i : Fin q) → Finpartition (block i) := fun i => shiftPartition25 (i.1 * B) P
  have hind : (Finset.univ : Finset (Fin q)).SupIndep block := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, Finset.mem_univ,
      Function.onFun, id_eq, ne_eq, forall_const]
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [block, shift25, Finset.mem_image, Finset.mem_Icc] at hxi hxj
    obtain ⟨u, ⟨hu1, huB⟩, hux⟩ := hxi
    obtain ⟨v, ⟨hv1, hvB⟩, hvx⟩ := hxj
    have heq : i.1 = j.1 := by nlinarith
    exact hij (Fin.ext heq)
  have hsup : (Finset.univ : Finset (Fin q)).sup block = Icc 1 (q * B) := by
    ext x
    simp only [Finset.mem_sup, Finset.mem_univ, true_and, block, shift25,
      Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨i, y, ⟨hy1, hyB⟩, rfl⟩
      constructor
      · omega
      · have hi := i.isLt
        nlinarith
    · rintro ⟨hx1, hxq⟩
      let i : Fin q := ⟨(x - 1) / B, by
        apply (Nat.div_lt_iff_lt_mul hB).2
        omega⟩
      let y := (x - 1) % B + 1
      refine ⟨i, y, ?_, ?_⟩
      · constructor
        · omega
        · have hm := Nat.mod_lt (x - 1) hB
          omega
      · dsimp [i, y]
        calc
          (x - 1) / B * B + ((x - 1) % B + 1) =
              (x - 1) % B + B * ((x - 1) / B) + 1 := by ac_rfl
          _ = x := by
            calc
              (x - 1) % B + B * ((x - 1) / B) + 1 = (x - 1) + 1 :=
                congrArg (· + 1) (Nat.mod_add_div (x - 1) B)
              _ = x := Nat.sub_add_cancel hx1
  exact {
    parts := (Finset.univ : Finset (Fin q)).biUnion fun i => (part i).parts
    supIndep := Finset.SupIndep.biUnion (by
      change (Finset.univ : Finset (Fin q)).SupIndep
        (fun i => (part i).parts.sup id)
      have heq : (fun i => (part i).parts.sup id) = block := by
        funext i
        exact (part i).sup_parts
      rw [heq]
      exact hind)
      (fun i _ => (part i).supIndep)
    sup_parts := by
      rw [Finset.sup_biUnion]
      calc
        (Finset.univ : Finset (Fin q)).sup (fun i => (part i).parts.sup id) =
            (Finset.univ : Finset (Fin q)).sup block := by
              apply Finset.sup_congr rfl
              intro i _
              exact (part i).sup_parts
        _ = Icc 1 (q * B) := hsup
    bot_notMem := by
      rw [Finset.mem_biUnion]
      push_neg
      exact fun i _ => (part i).bot_notMem }

private lemma repeatPartition25_card_le {B : ℕ} (q : ℕ) (hB : 0 < B)
    (P : Finpartition (Icc 1 B)) :
    #(repeatPartition25 q hB P).parts ≤ q * #P.parts := by
  simp only [repeatPartition25]
  rw [show q * #P.parts = ∑ _i : Fin q, #P.parts by simp]
  calc
    _ ≤ ∑ i : Fin q, #(shiftPartition25 (i.1 * B) P).parts :=
      Finset.card_biUnion_le
    _ = _ := by simp [shiftPartition25_card]

private lemma restrictedSumset_shift25 (a : ℕ) (s : Finset ℕ) :
    (shift25 a s).restrictedSumset = shift25 (2 * a) s.restrictedSumset := by
  ext z
  simp only [Finset.restrictedSumset, Finset.mem_image, Finset.mem_offDiag, shift25,
    Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨⟨u, hu, hux⟩, ⟨v, hv, hvy⟩, hxy⟩, rfl⟩
    subst x
    subst y
    refine ⟨u + v, ⟨u, v, ⟨hu, hv, ?_⟩, rfl⟩, ?_⟩
    · intro huv
      apply hxy
      omega
    · omega
  · rintro ⟨w, ⟨u, v, ⟨hu, hv, huv⟩, rfl⟩, rfl⟩
    refine ⟨a + u, a + v, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact ⟨u, hu, rfl⟩
    · exact ⟨v, hv, rfl⟩
    · intro h
      apply huv
      omega
    · omega

private lemma repeatPartition25_sum_le {B : ℕ} (q : ℕ) (hB : 0 < B)
    (P : Finpartition (Icc 1 B)) :
    #((repeatPartition25 q hB P).parts.biUnion Finset.restrictedSumset) ≤
      q * #(P.parts.biUnion Finset.restrictedSumset) := by
  let U := (Finset.univ : Finset (Fin q)).biUnion fun i =>
    shift25 (2 * (i.1 * B)) (P.parts.biUnion Finset.restrictedSumset)
  have hsub : (repeatPartition25 q hB P).parts.biUnion Finset.restrictedSumset ⊆ U := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    simp only [repeatPartition25, Finset.mem_biUnion, Finset.mem_univ, true_and] at hp
    obtain ⟨i, hp⟩ := hp
    change p ∈ P.parts.image (shift25 (i.1 * B)) at hp
    rw [Finset.mem_image] at hp
    obtain ⟨p0, hp0, rfl⟩ := hp
    rw [restrictedSumset_shift25] at hzp
    dsimp [U]
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [shift25, Finset.mem_image] at hzp ⊢
    obtain ⟨w, hw, rfl⟩ := hzp
    refine ⟨w, ?_, rfl⟩
    rw [Finset.mem_biUnion]
    exact ⟨p0, hp0, hw⟩
  calc
    _ ≤ #U := Finset.card_le_card hsub
    _ ≤ ∑ i : Fin q, #(shift25 (2 * (i.1 * B))
        (P.parts.biUnion Finset.restrictedSumset)) := Finset.card_biUnion_le
    _ = q * #(P.parts.biUnion Finset.restrictedSumset) := by
      have hc : ∀ i : Fin q, #(shift25 (2 * (i.1 * B))
          (P.parts.biUnion Finset.restrictedSumset)) =
          #(P.parts.biUnion Finset.restrictedSumset) := by
        intro i
        exact Finset.card_image_iff.mpr fun _ _ _ _ h => Nat.add_left_cancel h
      simp_rw [hc]
      simp

private lemma restrict_partition25 {s t : Finset ℕ} (P : Finpartition s) (ht : t ⊆ s) :
    ∃ Q : Finpartition t,
      #Q.parts ≤ #P.parts ∧
      Q.parts.biUnion Finset.restrictedSumset ⊆
        P.parts.biUnion Finset.restrictedSumset := by
  let raw := P.parts.image (fun p => p ∩ t)
  have hind : raw.SupIndep id := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, raw, Finset.mem_image]
    rintro A ⟨p, hp, rfl⟩ B ⟨q, hq, rfl⟩ hAB
    exact (P.disjoint hp hq (fun h => hAB (congrArg (fun u => u ∩ t) h))).mono
      (Finset.inter_subset_left) (Finset.inter_subset_left)
  have hsup : raw.sup id = t := by
    apply Finset.ext
    intro x
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨u, hu, hxu⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
      exact (Finset.mem_inter.mp hxu).2
    · intro hxt
      obtain ⟨p, hp, hxp⟩ := P.exists_mem (ht hxt)
      refine ⟨p ∩ t, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
      exact Finset.mem_inter.mpr ⟨hxp, hxt⟩
  let Q : Finpartition t := Finpartition.ofErase raw hind hsup
  refine ⟨Q, ?_, ?_⟩
  · calc
      #Q.parts ≤ #raw := Finset.card_erase_le
      _ ≤ #P.parts := Finset.card_image_le
  · intro z hz
    rw [Finset.mem_biUnion] at hz ⊢
    obtain ⟨u, huQ, hzu⟩ := hz
    change u ∈ (P.parts.image (fun p => p ∩ t)).erase ∅ at huQ
    have huRaw : u ∈ P.parts.image (fun p => p ∩ t) := (Finset.mem_erase.mp huQ).2
    obtain ⟨p, hp, hup⟩ := Finset.mem_image.mp huRaw
    subst u
    refine ⟨p, hp, ?_⟩
    rw [Finset.restrictedSumset] at hzu ⊢
    obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hzu
    refine Finset.mem_image.mpr ⟨xy, ?_, rfl⟩
    rw [Finset.mem_offDiag] at hxy ⊢
    exact ⟨(Finset.mem_inter.mp hxy.1).1,
      (Finset.mem_inter.mp hxy.2.1).1, hxy.2.2⟩

private def scale25 (t : ℕ) : ℕ := 2 ^ (4 * (2 ^ t) ^ 2)

private def level25 (N : ℕ) : ℕ := Nat.log 4 (Nat.log 2 N) - 1

private lemma scale25_exponent (t : ℕ) :
    4 * (2 ^ t) ^ 2 = 4 ^ (t + 1) := by
  conv_lhs =>
    rw [show 4 = 2 ^ 2 by norm_num]
    rw [← pow_mul]
    rw [← pow_add]
  conv_rhs =>
    rw [show 4 = 2 ^ 2 by norm_num]
    rw [← pow_mul]
  congr 1
  omega

private lemma level25_good (N : ℕ) (hL : 4 ^ 6 ≤ Nat.log 2 N) :
    5 ≤ level25 N ∧ scale25 (level25 N) ≤ N := by
  let L := Nat.log 2 N
  let u := Nat.log 4 L
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hu : 6 ≤ u := Nat.le_log_of_pow_le (by omega) (by simpa [L] using hL)
  have ht : level25 N + 1 = u := by
    change u - 1 + 1 = u
    omega
  have hN0 : N ≠ 0 := by
    intro h
    subst N
    simp [L] at hLpos
  have hE : 4 ^ (level25 N + 1) ≤ L := by
    rw [ht]
    exact Nat.pow_log_le_self 4 hLpos.ne'
  constructor
  · change 5 ≤ u - 1
    omega
  · rw [scale25, scale25_exponent]
    exact (Nat.pow_le_pow_right (by omega) hE).trans
      (Nat.pow_log_le_self 2 hN0)

private noncomputable def fallbackPartition25 (N : ℕ) : Finpartition (Icc 1 N) := by
  let s : Setoid ℕ := ⊤
  letI : DecidableRel s.r := Classical.decRel _
  exact Finpartition.ofSetSetoid s _

/-! ## The construction: the maximal number of complemented digits

`complemented_digit_partition Q m r` holds for every `r ≤ m`, and its sumset budget is linear in
`r` against a denominator of order `Q = 2^(4m)`. So `r` can be taken up to `r = m = 2^t`, giving
`N / exp(√(log N) / 16)` parts. -/

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

/-! ## Tiling `[1, N]` with copies of a base partition

The tiling argument only uses the base partition's part count and sumset bound. -/

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
    strongUpper =o[atTop] fun N : ℕ => (N : ℝ) / (Real.log N) ^ k := by
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
  show ‖strongUpper N‖ ≤ c * ‖(N : ℝ) / (Real.log (N : ℝ)) ^ k‖
  rw [strongUpper, Real.norm_eq_abs, Real.norm_eq_abs,
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
    strongUpper =o[atTop] bestUpper := by
  have h := strongUpper_isLittleO_polylog 1
  have he : (fun N : ℕ => (N : ℝ) / (Real.log N) ^ 1) = bestUpper := by
    funext N
    rw [pow_one, bestUpper]
  rwa [he] at h

/-! ## The solution -/

/-- **Green 25, upper bound.** Statement verbatim from formal-conjectures, with
`answer(sorry)` filled in by the explicit function `strongAnswer`. -/
theorem green_25.upper :
    let ans := (answer(strongAnswer) : ℕ → ℕ)
    (∀ᶠ N in atTop, 1 ≤ ans N ∧ ans N ≤ N) ∧ -- Ensure k is a valid partition size
    (fun N => (ans N : ℝ)) =o[atTop] bestUpper ∧
    ¬ ∀ᶠ N in atTop, Property25 (ans N) N := by
  intro ans
  refine ⟨strongAnswer_size, ?_, ?_⟩
  · exact strongAnswer_isBigO.trans_isLittleO strongUpper_isLittleO_bestUpper
  · exact Filter.not_eventually.2 strongAnswer_not_property.frequently

/-- **The rate the answer achieves.** `strongAnswer N = O(N / exp(√(log N) / 16))`, and
consequently `strongAnswer N = o(N / (log N)^k)` for every fixed `k`. formal-conjectures only
asks for `o(N / log N)`. -/
theorem strongAnswer_rate :
    (fun N => (strongAnswer N : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / Real.exp (Real.sqrt (Real.log N) / 16)) ∧
    ∀ k : ℕ, (fun N => (strongAnswer N : ℝ)) =o[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log N) ^ k) :=
  ⟨strongAnswer_isBigO, fun k => strongAnswer_isBigO.trans_isLittleO (strongUpper_isLittleO_polylog k)⟩

end AtlasFCSolutions.Green25

#print axioms AtlasFCSolutions.Green25.green_25.upper
#print axioms AtlasFCSolutions.Green25.strongAnswer_rate
