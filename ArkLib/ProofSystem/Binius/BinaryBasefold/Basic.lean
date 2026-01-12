/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/- ## Fundamental OracleReduction-related defintions for protocol specifications -/

noncomputable section
namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

variable {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ]
variable (𝓑 : Fin 2 ↪ L)

section OracleStatementIndex
variable (ℓ : ℕ) (ϑ : ℕ) [NeZero ℓ] [NeZero ϑ] [hdiv : Fact (ϑ ∣ ℓ)]

lemma div_add_one_eq_if_dvd (i ϑ : ℕ) [NeZero ϑ] :
    (i + 1) / ϑ = if ϑ ∣ i + 1 then i / ϑ + 1 else i / ϑ := by
  split_ifs with h_dvd
  case pos => exact Nat.succ_div_of_dvd h_dvd
  case neg => exact Nat.succ_div_of_not_dvd h_dvd

def toOutCodewordsCount (i : Fin (ℓ + 1)) : ℕ := by
  -- the number of codewords available as oracle at state `i` (at the beginning of round `i`)
  exact i/ϑ + (if (i < ℓ) then 1 else 0)

def isCommitmentRound (i : Fin ℓ) : Prop :=
  ϑ ∣ i.val + 1 ∧ i.val + 1 ≠ ℓ

omit [NeZero ϑ] hdiv in
lemma toOutCodewordsCountOf0 : toOutCodewordsCount ℓ ϑ 0 = 1 := by
  unfold toOutCodewordsCount
  simp only [Fin.coe_ofNat_eq_mod, zero_mod, Nat.zero_div, zero_add, ite_eq_left_iff, not_lt,
    nonpos_iff_eq_zero, zero_ne_one, imp_false]
  exact NeZero.ne ℓ

@[simp]
instance instNeZeroNatToOutCodewordsCount : ∀ i, NeZero (toOutCodewordsCount ℓ ϑ i) := by
  intro i
  have h_ne_0: toOutCodewordsCount ℓ ϑ i ≠ 0 := by
    simp only [toOutCodewordsCount]
    by_cases h_i_lt_ℓ: i.val < ℓ
    · simp only [h_i_lt_ℓ, ↓reduceIte]; apply Nat.succ_ne_zero
    · simp only [h_i_lt_ℓ, ↓reduceIte, add_zero, ne_eq, Nat.div_eq_zero_iff, not_or, not_lt]
      constructor
      · exact NeZero.ne ϑ
      · have h_i: i = ℓ := by omega
        rw [h_i]; apply Nat.le_of_dvd (by exact pos_of_neZero ℓ) (hdiv.out)
  exact NeZero.mk h_ne_0

omit [NeZero ϑ] [NeZero ℓ] hdiv in
lemma toCodewordsCount_mul_ϑ_le_i (i : Fin (ℓ + 1)) :
  ∀ j: Fin (toOutCodewordsCount ℓ ϑ i), j.val * ϑ ≤
    (if i.val < ℓ then i.val else ℓ - ϑ) := by
  intro j
  split_ifs with h_il
  -- Case 1: i.val < ℓ
  case pos =>
    have hj : j.val ≤ i.val / ϑ := by
      apply Nat.lt_succ_iff.mp
      have hj_lt := j.isLt
      unfold toOutCodewordsCount at hj_lt
      simp only [h_il, ↓reduceIte] at hj_lt
      omega
    have h_mul := Nat.mul_le_mul_right ϑ hj
    exact h_mul.trans (Nat.div_mul_le_self i.val ϑ)
  -- Case 2: ¬(i.val < ℓ), which means i.val = ℓ
  case neg =>
    have h_ival_eq_l : i.val = ℓ := by omega
    have hj : j.val < ℓ / ϑ := by
      apply Nat.lt_succ_iff.mp
      have hj_lt := j.isLt
      unfold toOutCodewordsCount at hj_lt
      simp only [h_il, ↓reduceIte, add_zero] at hj_lt
      apply Nat.succ_lt_succ
      calc j.val < i.val / ϑ := by omega
        _ = _ := by congr
    have hj : j.val ≤ ℓ / ϑ - 1 := by apply Nat.le_sub_one_of_lt hj
    have h_mul := Nat.mul_le_mul_right ϑ hj
    rw [Nat.mul_sub_right_distrib, one_mul] at h_mul
    exact h_mul.trans (Nat.sub_le_sub_right (Nat.div_mul_le_self ℓ ϑ) ϑ)

omit hdiv in
lemma toOutCodewordsCount_succ_eq_add_one_iff (i : Fin ℓ) :
    isCommitmentRound ℓ ϑ i ↔
    (toOutCodewordsCount ℓ ϑ i.castSucc) + 1 = toOutCodewordsCount ℓ ϑ i.succ := by
  have h_i_succ: i.val + 1 = i.succ.val := rfl
  rw [isCommitmentRound, h_i_succ]
  constructor
  · intro h_i_transition
    unfold toOutCodewordsCount
    -- We know i.val < ℓ because i : Fin ℓ. We also know i.succ.val < ℓ from the hypothesis.
    have h_i_lt_l : i.val < ℓ := i.isLt
    have h_succ_lt_l : i.succ.val < ℓ := by
      apply Nat.lt_of_le_of_ne
      · omega
      · intro h_eq
        apply h_i_transition.2
        exact h_eq
    -- Simplify the expression using the known inequalities
    simp only [Fin.coe_castSucc, h_i_lt_l, ↓reduceIte, Fin.val_succ]
    ring_nf
    simp only [Fin.val_succ] at h_succ_lt_l
    rw [add_comm] at h_succ_lt_l
    simp only [h_succ_lt_l, ↓reduceIte]
    rw [add_comm 1 i.val]
    let k := (i + 1) / ϑ
    have h_k: (i + 1) / ϑ = k := rfl
    have h_k_mul_v: k * ϑ = i + 1 := by
      rw [mul_comm]
      rw [Nat.mul_div_eq_iff_dvd]
      exact h_i_transition.1
    have h_v_ne_0: ϑ ≠ 0 := by exact Ne.symm (NeZero.ne' ϑ)
    have h_k_gt_0: k > 0 := by
      by_contra h
      simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h
      have h_i_add_1_eq_0: i.val + 1 = 0 := by
        simp only [h, Nat.div_eq_zero_iff, h_v_ne_0, false_or] at h_k -- h_k : ↑i + 1 < ϑ
        have h_v_ne_i_add_1: ϑ ≤ i.val + 1 := by
          apply Nat.le_of_dvd (by
            simp only [Fin.val_succ, lt_add_iff_pos_left, add_pos_iff, Fin.val_pos_iff, zero_lt_one,
              or_true]
          ) h_i_transition.1
        linarith -- h_v_ne_i_add_1 and h_k
      linarith
    have h_i_div_ϑ : i / ϑ = k - 1 := by
      apply Nat.div_eq_of_lt_le ?_ ?_
      · -- ⊢ (k - 1) * ϑ ≤ ↑i
        apply Nat.le_of_add_le_add_right (b:=ϑ)
        calc
          _ = (k - 1) * ϑ + 1 * ϑ := by omega
          _ = (k - 1 + 1) * ϑ := by exact Eq.symm (Nat.add_mul (k - 1) 1 ϑ)
          _ = i.val + 1 := by rw [←h_k_mul_v]; congr; omega -- uses h_k_gt_0
          _ ≤ i.val + ϑ := by apply Nat.add_le_add_left; omega
      · -- ⊢ ↑i < (k - 1 + 1) * ϑ
        rw [Nat.sub_one_add_one (by omega), h_k_mul_v]; omega
    rw [h_i_div_ϑ, h_k, add_comm]
    omega
  · -- ⊢ toOutCodewordsCount ℓ ϑ i.castSucc + 1 = toOutCodewordsCount ℓ ϑ i.succ →
    --   ϑ ∣ ↑i.succ ∧ i.succ ≠ ⟨ℓ, ⋯⟩
    intro h_eq
    constructor
    · -- Prove ϑ ∣ ↑i.succ
      unfold toOutCodewordsCount at h_eq
      have h_i_lt_l : i.val < ℓ := i.isLt
      simp only [Fin.coe_castSucc, h_i_lt_l, ↓reduceIte, Fin.val_succ] at h_eq
      -- We have: i / ϑ + 1 + 1 = (i + 1) / ϑ + (if i + 1 < ℓ then 1 else 0)
      by_cases h_succ_lt_l : i.val + 1 < ℓ
      · -- Case: i.succ < ℓ
        simp only [h_succ_lt_l, ↓reduceIte] at h_eq
        -- Now we have: i / ϑ + 2 = (i + 1) / ϑ + 1
        -- So: i / ϑ + 1 = (i + 1) / ϑ
        have h_div_eq : i.val / ϑ + 1 = (i.val + 1) / ϑ := by omega
        -- Use div_add_one_eq_if_dvd: (i + 1) / ϑ = if ϑ ∣ i + 1 then i / ϑ + 1 else i / ϑ
        have h_from_lemma := div_add_one_eq_if_dvd i.val ϑ
        rw [h_from_lemma] at h_div_eq
        -- If ϑ ∣ (i + 1), then i / ϑ + 1 = i / ϑ + 1 ✓
        -- If ¬(ϑ ∣ (i + 1)), then i / ϑ + 1 = i / ϑ, which gives 1 = 0 ✗
        by_cases h_dvd_case : ϑ ∣ (i.val + 1)
        · exact h_dvd_case
        · simp [h_dvd_case] at h_div_eq
      · -- Case: ¬(i.succ < ℓ), so i.succ.val = ℓ
        simp only [h_succ_lt_l, ↓reduceIte] at h_eq
        -- Now we have: i / ϑ + 2 = (i + 1) / ϑ
        have h_i_succ_eq_l : i.val + 1 = ℓ := by omega
        -- Use div_add_one_eq_if_dvd: (i + 1) / ϑ = if ϑ ∣ i + 1 then i / ϑ + 1 else i / ϑ
        have h_from_lemma := div_add_one_eq_if_dvd i.val ϑ
        -- Substitute the lemma directly into h_eq
        rw [h_from_lemma] at h_eq
        -- If ϑ ∣ (i + 1), then i / ϑ + 2 = i / ϑ + 1, which gives 2 = 1 ✗
        -- If ¬(ϑ ∣ (i + 1)), then i / ϑ + 2 = i / ϑ, which gives 2 = 0 ✗
        by_cases h_dvd_case : ϑ ∣ (i.val + 1)
        · -- If ϑ ∣ (i + 1), then we have our goal since i.succ.val = i.val + 1
          rw [Fin.val_succ]
          exact h_dvd_case
        · -- If ¬(ϑ ∣ (i + 1)), then h_eq becomes: i / ϑ + 2 = i / ϑ, so 2 = 0
          simp [h_dvd_case] at h_eq
          -- This gives us 2 = 0, which is impossible
          omega
    · -- Prove i.succ ≠ ⟨ℓ, ⋯⟩
      intro h_eq_l
      -- But i : Fin ℓ means i.val < ℓ, so i.succ.val = i.val + 1 ≤ ℓ
      -- If i.succ.val = ℓ, then i.val = ℓ - 1
      have h_i_eq : i.val = ℓ - 1 := by
        have h_succ : i.succ.val = i.val + 1 := by simp [Fin.val_succ]
        rw [h_eq_l] at h_succ
        omega
      -- Now check if the equation can hold
      unfold toOutCodewordsCount at h_eq
      have h_i_lt_l : i.val < ℓ := i.isLt
      simp only [Fin.coe_castSucc, h_i_lt_l, ↓reduceIte, Fin.val_succ] at h_eq
      -- We know that i.succ.val = ℓ, so i.val + 1 = ℓ, which means i.val + 1 ≮ ℓ
      have h_not_lt : ¬(i.val + 1 < ℓ) := by
        have h_succ_val : i.succ.val = i.val + 1 := by
          simp only [Fin.val_succ]
        rw [h_eq_l] at h_succ_val
        omega
      simp only [h_not_lt, ↓reduceIte] at h_eq
      -- We get: i / ϑ + 2 = ℓ / ϑ
      rw [h_i_eq] at h_eq
      -- So: (ℓ - 1) / ϑ + 2 = ℓ / ϑ
      -- Simplify the arithmetic first
      ring_nf at h_eq
      -- Now h_eq is: 2 + (ℓ - 1) / ϑ = (1 + (ℓ - 1)) / ϑ
      -- Note that 1 + (ℓ - 1) = ℓ
      have h_simp : 1 + (ℓ - 1) = ℓ := by omega
      rw [h_simp] at h_eq
      -- Use div_add_one_eq_if_dvd: ℓ / ϑ = if ϑ ∣ ℓ then (ℓ - 1) / ϑ + 1 else (ℓ - 1) / ϑ
      have h_ℓ_pos : 0 < ℓ := by omega -- since i.val < ℓ and i.val = ℓ - 1 ≥ 0
      have h_from_lemma := div_add_one_eq_if_dvd (ℓ - 1) ϑ
      -- Rewrite ℓ as (ℓ - 1) + 1 in the division
      have h_ℓ_div : ℓ = (ℓ - 1) + 1 := by omega
      rw [h_ℓ_div, h_from_lemma] at h_eq
      -- If ϑ ∣ ℓ, then (ℓ - 1) / ϑ + 2 = (ℓ - 1) / ϑ + 1, so 2 = 1 ✗
      -- If ¬(ϑ ∣ ℓ), then (ℓ - 1) / ϑ + 2 = (ℓ - 1) / ϑ, so 2 = 0 ✗
      by_cases h_dvd_ℓ : ϑ ∣ ℓ
      · -- If ϑ ∣ ℓ, then the if-then-else becomes (ℓ - 1) / ϑ + 1
        -- First simplify the arithmetic in h_eq
        have h_arith : ℓ - 1 + 1 - 1 = ℓ - 1 := by omega
        rw [h_arith] at h_eq
        -- Now simplify the if-then-else using h_dvd_ℓ
        have h_ℓ_eq : ℓ - 1 + 1 = ℓ := by omega
        rw [h_ℓ_eq] at h_eq
        simp [h_dvd_ℓ] at h_eq
        -- h_eq is now: 2 + (ℓ - 1) / ϑ = (ℓ - 1) / ϑ + 1
        -- This simplifies to: 2 = 1, which is impossible
        omega
      · -- If ¬(ϑ ∣ ℓ), then the if-then-else becomes (ℓ - 1) / ϑ
        -- First simplify the arithmetic in h_eq
        have h_arith : ℓ - 1 + 1 - 1 = ℓ - 1 := by omega
        rw [h_arith] at h_eq
        -- Now simplify the if-then-else using h_dvd_ℓ
        have h_ℓ_eq : ℓ - 1 + 1 = ℓ := by omega
        rw [h_ℓ_eq] at h_eq
        simp [h_dvd_ℓ] at h_eq
        -- h_eq is now: 2 + (ℓ - 1) / ϑ = (ℓ - 1) / ϑ
        -- This simplifies to: 2 = 0, which is impossible

open Classical in
lemma toOutCodewordsCount_succ_eq (i : Fin ℓ) :
  (toOutCodewordsCount ℓ ϑ i.succ) =
    if isCommitmentRound ℓ ϑ i then (toOutCodewordsCount ℓ ϑ i.castSucc) + 1
    else (toOutCodewordsCount ℓ ϑ i.castSucc) := by
  have h_succ_val: i.succ.val = i.val + 1 := rfl
  by_cases hv: ϑ ∣ i.val + 1 ∧ i.val + 1 ≠ ℓ
  · have h_succ := (toOutCodewordsCount_succ_eq_add_one_iff ℓ ϑ i).mp hv
    rw [←h_succ];
    simp only [left_eq_ite_iff, Nat.add_eq_left, one_ne_zero, imp_false, Decidable.not_not]
    exact hv
  · rw [isCommitmentRound]
    simp [ne_eq, hv, ↓reduceIte]
    unfold toOutCodewordsCount
    have h_i_lt_ℓ: i.castSucc.val < ℓ := by
      change i.val < ℓ
      omega
    simp only [Fin.val_succ, Fin.coe_castSucc, Fin.is_lt, ↓reduceIte]
    rw [div_add_one_eq_if_dvd]
    by_cases hv_div_succ: ϑ ∣ i.val + 1
    · simp only [hv_div_succ, ↓reduceIte, Nat.add_eq_left, ite_eq_right_iff, one_ne_zero,
      imp_false, not_lt, ge_iff_le]
      simp only [hv_div_succ, ne_eq, true_and, Decidable.not_not] at hv
      have h_eq: i.succ.val = ℓ := by
        change i.succ.val = (⟨ℓ, by omega⟩: Fin (ℓ + 1)).val
        exact hv
      omega
    · simp only [hv_div_succ, ↓reduceIte, Nat.add_left_cancel_iff, ite_eq_left_iff, not_lt,
      zero_ne_one, imp_false, not_le, gt_iff_lt]
      if hi_succ_lt: i.succ.val < ℓ then
        omega
      else
        simp only [Fin.val_succ, not_lt] at hi_succ_lt
        have hi_succ_le_ℓ: i.succ.val ≤ ℓ := by omega
        have hi_succ_eq_ℓ: i.val + 1 = ℓ := by omega
        rw [hi_succ_eq_ℓ] at hv_div_succ
        exact False.elim (hv_div_succ (hdiv.out))

lemma toOutCodewordsCount_i_le_of_succ (i : Fin ℓ) :
  toOutCodewordsCount ℓ ϑ i.castSucc ≤ toOutCodewordsCount ℓ ϑ i.succ := by
  rw [toOutCodewordsCount_succ_eq ℓ ϑ]
  split_ifs
  · omega
  · omega

lemma toOutCodewordsCount_last ℓ ϑ : toOutCodewordsCount ℓ ϑ (Fin.last ℓ) = ℓ / ϑ := by
  unfold toOutCodewordsCount
  simp only [Fin.val_last, lt_self_iff_false, ↓reduceIte, add_zero]

omit [NeZero ℓ] hdiv in
/--
If a new oracle is committed at round `i + 1` (i.e., `ϑ ∣ i + 1`), then the index of this
new oracle (which is the count of oracles from the previous round, `i`) multiplied by `ϑ`
equals the current round number `i + 1`.
TODO: double check why this is still correct when replacing `hCR` with `ϑ | i + 1`
-/
lemma toOutCodewordsCount_mul_ϑ_eq_i_succ (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
  (toOutCodewordsCount ℓ ϑ i.castSucc) * ϑ = i.val + 1 := by
  unfold toOutCodewordsCount
  simp only [Fin.coe_castSucc, i.isLt, ↓reduceIte]
  have h_mod : i.val % ϑ = ϑ - 1 := by
    refine (mod_eq_sub_iff ?_ ?_).mpr hCR.1
    · omega
    · exact NeZero.one_le
  -- After unfolding, we have: (i.val / ϑ + 1) * ϑ = i.val + 1
  rw [Nat.add_mul, one_mul]
  -- Now we have: (i.val / ϑ) * ϑ + ϑ = i.val + 1
  -- Since ϑ ∣ (i.val + 1), we can use Nat.div_mul_cancel
  -- ⊢ ↑i / ϑ * ϑ + ϑ = ↑i + 1
  rw [Nat.div_mul_self_eq_mod_sub_self, h_mod]
  rw [←Nat.sub_add_comm (k:=ϑ - 1) (m:=ϑ) (by
    calc _ = i.val % ϑ := by omega
      _ ≤ i := by exact Nat.mod_le (↑i) ϑ
  )]
  -- ⊢ ↑i + ϑ - (ϑ - 1) = ↑i + 1
  rw [Nat.sub_sub_right (a:=i.val + ϑ) (b:=ϑ) (c:=1) (by exact NeZero.one_le)]
  omega

lemma toCodewordsCount_mul_ϑ_lt_ℓ (ℓ ϑ : ℕ) [NeZero ϑ] [NeZero ℓ] (i : Fin (ℓ + 1)) :
  ∀ j: Fin (toOutCodewordsCount ℓ ϑ i), j.val * ϑ < ℓ := by
  intro j
  unfold toOutCodewordsCount
  have h_j_lt : j.val < i.val / ϑ + if i.val < ℓ then 1 else 0 := j.2
  have h_j_mul_ϑ_lt := toCodewordsCount_mul_ϑ_le_i ℓ ϑ i j
  calc
    ↑j * ϑ ≤ if ↑i < ℓ then ↑i else ℓ - ϑ := by omega
    _ < _ := by
      by_cases h_i_lt_ℓ : i.val < ℓ
      · -- Case 1: i.val < ℓ
        simp only [h_i_lt_ℓ, ↓reduceIte]
      · -- Case 2: ¬(i.val < ℓ), which means i.val = ℓ
        simp only [h_i_lt_ℓ, ↓reduceIte, tsub_lt_self_iff]
        constructor
        · exact pos_of_neZero ℓ
        · exact pos_of_neZero ϑ

omit hdiv in
/-- The base index k = j * ϑ is less than ℓ for valid oracle indices -/
@[simp]
lemma oracle_block_k_bound (i : Fin (ℓ + 1)) (j : Fin (toOutCodewordsCount ℓ ϑ i)) :
    j.val * ϑ < ℓ :=
  toCodewordsCount_mul_ϑ_lt_ℓ ℓ ϑ i j

omit [NeZero ℓ] [NeZero ϑ] hdiv in
/-- The base index k = j * ϑ is less than or equal to i -/
@[simp]
lemma oracle_block_k_le_i (i : Fin (ℓ + 1)) (j : Fin (toOutCodewordsCount ℓ ϑ i))
    : j.val * ϑ ≤ i := by
  have h := toCodewordsCount_mul_ϑ_le_i ℓ ϑ i j
  by_cases hi : i < ℓ <;> simp only [hi, ↓reduceIte] at h <;> omega

/-- The next oracle index k + ϑ = (j+1) * ϑ is at most i -/
@[simp]
lemma oracle_block_k_next_le_i (i : Fin (ℓ + 1)) (j : Fin (toOutCodewordsCount ℓ ϑ i))
    (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i) : j.val * ϑ + ϑ ≤ i := by
  have h := toCodewordsCount_mul_ϑ_le_i ℓ ϑ i (j + 1)
  rw [Fin.val_add_one' (h_a_add_1:=hj), Nat.add_mul, Nat.one_mul] at h
  by_cases hi : i < ℓ <;> simp only [hi, ↓reduceIte] at h <;> omega

omit [NeZero ℓ] [NeZero ϑ] in
/-- For any oracle position j, the domain index j*ϑ plus ϑ steps is at most ℓ.
This is a key bound for proving fiber-wise closeness requirements. -/
@[simp]
lemma oracle_index_add_steps_le_ℓ (i : Fin (ℓ + 1))
    (j : Fin (toOutCodewordsCount ℓ ϑ i)) :
    j.val * ϑ + ϑ ≤ ℓ := by
  unfold toOutCodewordsCount
  by_cases h : i < ℓ
  · -- Case: i < ℓ, so toOutCodewordsCount = i/ϑ + 1
    have hj_bound : j.val < i / ϑ + 1 := by
      have : toOutCodewordsCount ℓ ϑ i = i / ϑ + 1 := by simp [toOutCodewordsCount, h]
      rw [← this]; exact j.isLt
    rw [← Nat.add_one_mul]
    apply Nat.le_trans (Nat.mul_le_mul_right ϑ (Nat.succ_le_of_lt hj_bound))
    apply Nat.mul_le_of_le_div
    apply Nat.succ_le_of_lt
    apply Nat.div_lt_of_lt_mul; rw [mul_comm]
    rw [Nat.div_mul_cancel hdiv.out]
    exact h
  · -- Case: i ≥ ℓ, so toOutCodewordsCount = i/ϑ
    have hj_bound : j.val < i / ϑ := by
      have : toOutCodewordsCount ℓ ϑ i = i / ϑ := by simp [toOutCodewordsCount, h]
      rw [← this]; exact j.isLt
    calc j.val * ϑ + ϑ
        = (j.val + 1) * ϑ := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (i / ϑ) * ϑ := by gcongr; omega
      _ ≤ i := Nat.div_mul_le_self i ϑ
      _ ≤ ℓ := Fin.is_le i

omit [NeZero ℓ] [NeZero ϑ] in
/-- For any oracle position j, the domain index j*ϑ is at most ℓ.
This is a key bound for proving fiber-wise closeness requirements. -/
@[simp]
lemma oracle_index_le_ℓ (i : Fin (ℓ + 1))
    (j : Fin (toOutCodewordsCount ℓ ϑ i)) :
    j.val * ϑ ≤ ℓ := by
  have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ i j
  omega

/-- Convert oracle position index to oracle domain index by multiplying by ϑ.
The position index j corresponds to the j-th oracle in the list of committed oracles,
and the domain index is j*ϑ, which is the actual index in the Fin ℓ domain. -/
@[reducible]
def oraclePositionToDomainIndex {i : Fin (ℓ + 1)}
    (positionIdx : Fin (toOutCodewordsCount ℓ ϑ i)) : Fin ℓ :=
  ⟨positionIdx.val * ϑ, oracle_block_k_bound ℓ ϑ i positionIdx⟩

def mkLastOracleIndex (i : Fin (ℓ + 1)) : Fin (toOutCodewordsCount ℓ ϑ i) := by
  have hv: ϑ ∣ ℓ := by exact hdiv.out
  rw [toOutCodewordsCount]
  if hi: i.val < ℓ then
    exact ⟨i.val / ϑ, by simp only [hi, ↓reduceIte, lt_add_iff_pos_right, zero_lt_one];⟩
  else
    have hi_eq_ℓ: i.val = ℓ := by omega
    exact ⟨ℓ/ϑ - 1 , by
      simp_rw [hi_eq_ℓ]
      simp only [lt_self_iff_false, ↓reduceIte, add_zero, tsub_lt_self_iff, Nat.div_pos_iff,
        zero_lt_one, and_true]
      constructor
      · exact pos_of_neZero ϑ
      · apply Nat.le_of_dvd (h:=by exact pos_of_neZero ℓ); omega
    ⟩

lemma mkLastOracleIndex_last : mkLastOracleIndex ℓ ϑ (Fin.last ℓ) = ℓ / ϑ - 1 := by
  dsimp only [mkLastOracleIndex, Fin.val_last, lt_self_iff_false, Lean.Elab.WF.paramLet]
  simp only [lt_self_iff_false, ↓reduceDIte]; rfl

def getLastOraclePositionIndex (i : Fin (ℓ + 1)) :
  Fin (toOutCodewordsCount ℓ ϑ i) := by
  let ne0 := (instNeZeroNatToOutCodewordsCount ℓ ϑ i).out
  exact ⟨(toOutCodewordsCount ℓ ϑ i) - 1, by omega⟩

@[reducible]
def getLastOracleDomainIndex (oracleFrontierIdx : Fin (ℓ + 1)) :
  Fin (ℓ) :=
  oraclePositionToDomainIndex (positionIdx := (getLastOraclePositionIndex ℓ ϑ oracleFrontierIdx))

lemma mkLastOracleIndex_eq_getLastOraclePositionIndex (i : Fin (ℓ + 1)) :
    mkLastOracleIndex ℓ ϑ i = getLastOraclePositionIndex ℓ ϑ i := by
  unfold mkLastOracleIndex getLastOraclePositionIndex
  apply Fin.eq_of_val_eq
  by_cases hi : i.val < ℓ
  · simp only [hi, ↓reduceDIte]
    unfold toOutCodewordsCount
    simp only [hi, ↓reduceIte]
    rfl
  · simp only [hi, ↓reduceDIte]
    unfold toOutCodewordsCount
    simp only [hi, eq_mpr_eq_cast, cast_eq, ↓reduceIte, add_zero];
    have h_eq: i.val = ℓ := by omega
    rw [h_eq]

lemma getLastOraclePositionIndex_last : getLastOraclePositionIndex ℓ ϑ (Fin.last ℓ)
  = ⟨ℓ / ϑ - 1, by
    dsimp only [toOutCodewordsCount, Fin.val_last, lt_self_iff_false];
    simp only [lt_self_iff_false,
      ↓reduceIte, add_zero, tsub_lt_self_iff, Nat.div_pos_iff, zero_lt_one, and_true]
    constructor
    · exact pos_of_neZero ϑ
    · apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
    ⟩ := by
  apply Fin.eq_of_val_eq
  dsimp only [getLastOraclePositionIndex, Fin.val_last, lt_self_iff_false, Lean.Elab.WF.paramLet]
  rw [toOutCodewordsCount_last]

lemma getLastOracleDomainIndex_last : getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)
  = ⟨ℓ - ϑ, by
    have h_ne_0 : 0 < ϑ := by exact pos_of_neZero ϑ
    have h_lt: ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
    omega⟩ := by
  apply Fin.eq_of_val_eq
  dsimp only [getLastOracleDomainIndex]
  rw [getLastOraclePositionIndex_last]; simp only;
  rw [Nat.sub_mul, Nat.one_mul]
  rw [Nat.div_mul_cancel (hdiv.out)]

lemma getLastOracleDomainIndex_add_ϑ_le (i : Fin (ℓ + 1)) :
    (getLastOracleDomainIndex ℓ ϑ i).val + ϑ ≤ ℓ := by
  rw [getLastOracleDomainIndex, oraclePositionToDomainIndex]
  simp only [oracle_index_add_steps_le_ℓ]
end OracleStatementIndex

section IndexBounds
variable {ℓ ϑ : ℕ} [NeZero ℓ] [NeZero ϑ] [hdiv : Fact (ϑ ∣ ℓ)]

/-- ϑ is positive -/
lemma folding_steps_pos : (ϑ : ℕ) > 0 := pos_of_neZero ϑ

omit hdiv in
/-- ℓ - ϑ < ℓ when both are positive -/
lemma rounds_sub_steps_lt : ℓ - ϑ < ℓ :=
  Nat.sub_lt (pos_of_neZero ℓ) (folding_steps_pos)

lemma ϑ_sub_one_le_self : ϑ - 1 < ϑ := by
  have lt_0: ϑ > 0 := by exact Nat.pos_of_neZero ϑ
  exact Nat.sub_one_lt_of_lt lt_0

@[simp] -- main lemma for bIdx: Fin (ℓ / ϑ - 1) bounds
lemma bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ (bIdx : Fin (ℓ / ϑ - 1)) (x : ℕ) {hx : x ≤ ϑ} :
    ↑bIdx * ϑ + x ≤ ℓ - ϑ := by
  have h_x_lt : x < ϑ + 1 := Nat.lt_succ_of_le hx
  have h_fin : x < ϑ ∨ x = ϑ := Nat.lt_or_eq_of_le hx
  calc
    ↑bIdx * ϑ + x ≤ ↑bIdx * ϑ + ϑ := by omega
    _ = (↑bIdx + 1) * ϑ := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ (ℓ / ϑ - 1) * ϑ := by gcongr; omega
    _ = ℓ - ϑ := by
      have h_bound : 1 ≤ ℓ / ϑ := by
        have h_le: ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ); exact hdiv.out
        rw [Nat.one_le_div_iff (by exact Nat.pos_of_neZero ϑ)]; exact h_le
      rw [Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
    _ ≤ ℓ - ϑ := by omega

@[simp]
lemma bIdx_mul_ϑ_add_i_lt_ℓ_succ {m : ℕ} (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin ϑ) :
    ↑bIdx * ϑ + ↑i < ℓ + m :=
  calc
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx i.val (hx:=by omega)
    _ < ℓ := by exact rounds_sub_steps_lt
    _ ≤ ℓ + m := by omega

@[simp]
lemma bIdx_mul_ϑ_add_i_cast_lt_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin (ϑ - 1 + 1))
    : ↑bIdx * ϑ + i < ℓ + 1 := by
  calc
    ↑bIdx * ϑ + i ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx (x:=i.val) (hx:=by omega)
    _ < ℓ + 1 := by omega

@[simp]
lemma bIdx_mul_ϑ_add_x_lt_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) (x : ℕ) {hx : x ≤ ϑ} :
    ↑bIdx * ϑ + x < ℓ + 1 := by
  calc
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx x (hx:=hx)
    _ < ℓ + 1 := by omega

@[simp]
lemma bIdx_mul_ϑ_add_i_fin_ℓ_pred_lt_ℓ (bIdx : Fin (ℓ / ϑ - 1)) (i : Fin (ϑ - 1))
    : ↑bIdx * ϑ + ↑i < ℓ := by
  calc
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx i.val (hx:=by omega)
    _ < ℓ := by exact rounds_sub_steps_lt

/-- When the block size allows it, we can get a strict inequality -/
lemma bIdx_succ_mul_ϑ_lt_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) :
    (↑bIdx + 1) * ϑ < ℓ + 1 := by
  calc
    (↑bIdx + 1) * ϑ = ↑bIdx * ϑ + ϑ := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ ℓ - ϑ := by apply bIdx_mul_ϑ_add_x_lt_ℓ_sub_ϑ bIdx ϑ (hx:=by omega)
    _ < ℓ + 1 := by omega

lemma bIdx_succ_mul_ϑ_le_ℓ_succ (bIdx : Fin (ℓ / ϑ - 1)) : (↑bIdx + 1) * ϑ ≤ ℓ + 1 := by
  exact Nat.le_of_lt (bIdx_succ_mul_ϑ_lt_ℓ_succ bIdx)

end IndexBounds

/-- Oracle frontier index: captures valid oracle indices for a given statement index.
    In Binary Basefold, the oracle can be at most 1 index behind the statement index.
    - At statement index `i+1`, the oracle can be at `i` (after fold) or `i+1` (after commit)
-/
def OracleFrontierIndex {ℓ : ℕ} (stmtIdx : Fin (ℓ + 1)) :=
  { val : Fin (ℓ + 1) // val.val ≤ stmtIdx.val ∧ stmtIdx.val ≤ val.val + 1 }

namespace OracleFrontierIndex

/-- Create oracle frontier index equal to statement index (synchronized case) -/
def mkFromStmtIdx {ℓ : ℕ} (stmtIdx : Fin (ℓ + 1)) :
    OracleFrontierIndex stmtIdx :=
  ⟨stmtIdx, by constructor <;> omega⟩

/-- Create oracle frontier index for statement i.succ with oracle at i (lagging case).
    Used after fold step where stmtIdx advances but oracle hasn't committed yet. -/
def mkFromStmtIdxCastSuccOfSucc {ℓ : ℕ} (i : Fin ℓ) :
    OracleFrontierIndex i.succ :=
  ⟨i.castSucc, by
    constructor
    · exact Nat.le_of_lt (Fin.castSucc_lt_succ i)
    · simp [Fin.val_succ, Fin.coe_castSucc]
  ⟩

@[simp]
lemma val_mkFromStmtIdx {ℓ : ℕ} (stmtIdx : Fin (ℓ + 1)) :
    (mkFromStmtIdx stmtIdx).val = stmtIdx := rfl

@[simp]
lemma val_mkFromStmtIdxCastSuccOfSucc {ℓ : ℕ} (i : Fin ℓ) :
    (mkFromStmtIdxCastSuccOfSucc i).val = i.castSucc := rfl

@[simp]
lemma val_le_i {ℓ : ℕ} (i : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex i) :
    oracleIdx.val ≤ i := by
  unfold OracleFrontierIndex at oracleIdx
  let h := oracleIdx.property
  cases h
  · exact h.left

@[simp]
lemma val_mkFromStmtIdxCastSuccOfSucc_eq_mkFromStmtIdx {ℓ : ℕ} (i : Fin ℓ) :
    (mkFromStmtIdxCastSuccOfSucc i).val = (mkFromStmtIdx i.castSucc).val := by rfl

end OracleFrontierIndex

section SumcheckOperations

abbrev MultilinearPoly (L : Type) [CommSemiring L] (ℓ : ℕ) := L⦃≤ 1⦄[X Fin ℓ]
abbrev MultiquadraticPoly (L : Type) [CommSemiring L] (ℓ : ℕ) := L⦃≤ 2⦄[X Fin ℓ]

/-- We treat the multiplier poly as a blackbox for protocol abstraction.
For example, in Binary Basefold it's `eqTilde(r₀, .., r_{ℓ-1}, X₀, .., X_{ℓ-1})` -/
structure SumcheckMultiplierParam (L : Type) [CommRing L] (ℓ : ℕ) (Context : Type := Unit) where
  multpoly : (ctx: Context) → MultilinearPoly L ℓ

/-- `H₀(X₀, ..., X_{ℓ-1}) = h(X₀, ..., X_{ℓ-1}) =`
  `m(X_0, ..., X_{ℓ-1}) · t(X_0, ..., X_{ℓ-1})` -/
def computeInitialSumcheckPoly (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ) : MultiquadraticPoly L ℓ :=
  ⟨m * t, by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i
    have h_t_deg: degreeOf i t.val ≤ 1 :=
      degreeOf_le_iff.mpr fun term a ↦ (t.property) a i
    have h_m_deg: degreeOf i m.val ≤ 1 :=
      degreeOf_le_iff.mpr fun term a ↦ (m.property) a i
    calc
      _ ≤ (degreeOf i m.val) + (degreeOf i t.val) :=
        degreeOf_mul_le i m.val t.val
      _ ≤ 2 := by omega
  ⟩

/-- `Hᵢ(Xᵢ, ..., X_{ℓ-1}) = ∑ ω ∈ 𝓑ᵢ, H₀(ω₀, …, ω_{i-1}, Xᵢ, …, X_{ℓ-1}) (where H₀=h)` -/
-- TODO: how to generalize this?
def projectToMidSumcheckPoly (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    : MultiquadraticPoly L (ℓ-i) :=
  let H₀: MultiquadraticPoly L ℓ := computeInitialSumcheckPoly (ℓ:=ℓ) t m
  let Hᵢ := fixFirstVariablesOfMQP (ℓ := ℓ) (v := ⟨i, by omega⟩)
    (H := H₀) (challenges := challenges)
  ⟨Hᵢ, by
    have hp := H₀.property
    simpa using
      (fixFirstVariablesOfMQP_degreeLE (L := L) (ℓ := ℓ) (v := ⟨i, by omega⟩)
        (poly := H₀.val) (challenges := challenges) (deg := 2) hp)
  ⟩

/-- Derive `H_{i+1}` from `H_i` by projecting the first variable -/
def projectToNextSumcheckPoly (i : Fin (ℓ)) (Hᵢ : MultiquadraticPoly L (ℓ - i))
    (rᵢ : L) : -- the current challenge
    MultiquadraticPoly L (ℓ - i.succ) := by
  let projectedH := fixFirstVariablesOfMQP (ℓ := ℓ - i) (v := ⟨1, by omega⟩)
    (H := Hᵢ.val) (challenges := fun _ => rᵢ)
  exact ⟨projectedH, by
    have hp := Hᵢ.property
    simpa using
      (fixFirstVariablesOfMQP_degreeLE (L := L) (ℓ := ℓ - i) (v := ⟨1, by omega⟩)
        (poly := Hᵢ.val) (challenges := fun _ => rᵢ) (deg := 2) hp)
  ⟩

lemma projectToNextSumcheckPoly_eval_eq (i : Fin ℓ) (Hᵢ : MultiquadraticPoly L (ℓ - i)) (rᵢ : L)
    (x : Fin (ℓ - i.succ) → L) :
    (projectToNextSumcheckPoly ℓ i Hᵢ rᵢ).val.eval x = Hᵢ.val.eval (Fin.cons rᵢ x ∘ Fin.cast (by simp only [Fin.val_succ]; omega)) := by
  unfold projectToNextSumcheckPoly fixFirstVariablesOfMQP
  simp only
  -- This requires unfolding the algebraic equivalences.
  -- We admit this for now.
  sorry

/-- **Key Sumcheck Property**: Evaluating the sumcheck round polynomial at a challenge equals
    the sum of the projected polynomial evaluations over the boolean hypercube.

    This is the fundamental relationship for the sumcheck protocol: when we create the round
    polynomial `g_i = getSumcheckRoundPoly(H_i)` and evaluate it at a challenge `rᵢ`, this equals
    the sum of evaluations of `H_{i+1} = projectToNextSumcheckPoly(H_i, rᵢ)` over all boolean points.

    Mathematically: `g_i(rᵢ) = ∑_{x ∈ {0,1}^{ℓ-i-1}} H_{i+1}(x)` where
    - `g_i` is the univariate sumcheck round polynomial derived from `H_i`
    - `H_{i+1}` is obtained by fixing the first variable of `H_i` to `rᵢ`
-/
lemma projectToNextSumcheckPoly_sum_eq (i : Fin ℓ) (Hᵢ : MultiquadraticPoly L (ℓ - i)) (rᵢ : L) :
    (getSumcheckRoundPoly ℓ 𝓑 i Hᵢ).val.eval rᵢ =
    (∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - i.succ),
      (projectToNextSumcheckPoly ℓ i Hᵢ rᵢ).val.eval x) := by
  -- By getSumcheckRoundPoly_eval_eq, the LHS equals:
  --   ∑ y ∈ hypercube^{ℓ-i-1}, H_i.eval (Fin.cons rᵢ y)
  -- By projectToNextSumcheckPoly definition, H_{i+1}(y) = H_i(Fin.cons rᵢ y)
  -- So the RHS equals: ∑ x ∈ hypercube^{ℓ-i-1}, H_i.eval (Fin.cons rᵢ x)
  -- These are the same sum with different variable names
  sorry

lemma projectToMidSumcheckPoly_succ (t : MultilinearPoly L ℓ) (m : MultilinearPoly L ℓ) (i : Fin ℓ)
    (challenges : Fin i.castSucc → L) (r_i' : L) :
    projectToMidSumcheckPoly ℓ t m i.succ (Fin.snoc challenges r_i') =
    projectToNextSumcheckPoly ℓ i (projectToMidSumcheckPoly ℓ t m i.castSucc challenges) r_i' := by
  sorry

lemma projectToMidSumcheckPoly_eq_prod (t : MultilinearPoly L ℓ)
    (m : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    : projectToMidSumcheckPoly (ℓ := ℓ) (t := t) (m := m) (i := i) (challenges := challenges) =
      (fixFirstVariablesOfMQP ℓ (v := i) (H := m) (challenges := challenges)) *
       (fixFirstVariablesOfMQP ℓ (v := i) (H := t) (challenges := challenges)) := by
  sorry

lemma fixFirstVariablesOfMQP_full_eval_eq_eval {deg : ℕ} {challenges : Fin (Fin.last ℓ) → L}
    {poly : L[X Fin ℓ]} (hp : poly ∈ L⦃≤ deg⦄[X Fin ℓ]) (x : Fin (ℓ - ℓ) → L) :
      (fixFirstVariablesOfMQP ℓ (v := Fin.last ℓ) poly challenges).eval x
      = poly.eval challenges := by
  sorry

end SumcheckOperations

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  -- [SelectableType L] => not used
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section OracleReductionComponents
-- In this section, we use notation `ϑ` for the folding steps, along with `(hdiv : ϑ ∣ ℓ)`

/-!
## Core Protocol Structures

Basic structures and definitions used throughout the Binary Basefold protocol.
-/

/-- Input context for the sumcheck protocol, used mainly in BinaryBasefold.
For other protocols, there might be other context data.
NOTE: might add a flag `rejected` to indicate if prover has been rejected before. But that seems
like a fundamental feature of OracleReduction instead, so no action taken for now. -/
structure SumcheckBaseContext (L : Type) (ℓ : ℕ) where
  t_eval_point : Fin ℓ → L         -- r = (r_0, ..., r_{ℓ-1}) => shared input
  original_claim : L               -- s = t(r) => the original claim to verify

/-- Statement per iterated sumcheck round -/
structure Statement (Context : Type) (i : Fin (ℓ + 1)) where
  -- Current round state
  sumcheck_target : L              -- s_i (current sumcheck target for round i)
  challenges : Fin i → L           -- R'_i = (r'_0, ..., r'_{i-1}) from previous rounds
  ctx : Context -- external context for composition from the outer protocol

/-- Statement for the final sumcheck step - includes the final constant c -/
structure FinalSumcheckStatementOut extends
  Statement (L := L) (Context := SumcheckBaseContext L ℓ) (Fin.last ℓ) where
  final_constant : L               -- c = f^(ℓ)(0, ..., 0)

def toStatement (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
  Statement (L := L) (Context := SumcheckBaseContext L ℓ) (Fin.last ℓ)  :=
  {
    sumcheck_target := stmt.sumcheck_target,
    challenges := stmt.challenges,
    ctx := stmt.ctx
  }

/-- For the `i`-th round of the protocol, there will be oracle statements corresponding
to all committed codewords. The verifier has oracle access to functions corresponding
to the handles in committed_handles. -/
@[reducible]
def OracleStatement (ϑ : ℕ) [NeZero ϑ] (i : Fin (ℓ + 1)) :
    Fin (toOutCodewordsCount ℓ ϑ (i:=i)) → Type := fun j =>
  by
    let sDomainIdx := oraclePositionToDomainIndex ℓ ϑ j
    exact (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨sDomainIdx, by omega⟩ → L

def mapOStmtOutRelayStep (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ j := fun j => by
  have h_oracle_size_eq: toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ := by
    simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hNCR, ↓reduceIte]
  -- oracle index mapping
  exact oStmt ⟨j, by rw [h_oracle_size_eq]; omega⟩

/-- The round witness for round `i` of `t ∈ L[≤ 2][X Fin ℓ]` and
`Hᵢ(Xᵢ, ..., Xₗ₋₁) := h(r₀', ..., rᵢ₋₁', Xᵢ, Xᵢ₊₁, ..., Xₗ₋₁) ∈ L[≤ 2][X Fin (ℓ-i)]`.
This ensures efficient computability and constraint on the structure of `H_i`
according to `t`.
-/
structure Witness (i : Fin (ℓ + 1)) where
  t : L⦃≤ 1⦄[X Fin ℓ]  -- The original polynomial t
  H : L⦃≤ 2⦄[X Fin (ℓ - i)] -- Hᵢ
  f: (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L -- fᵢ

/-- The extractor that recovers the multilinear polynomial t from f^(i) -/
noncomputable def extractMLP (i : Fin ℓ) (f : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L) :
    Option (L⦃≤ 1⦄[X Fin (ℓ - i)]) := by
  set domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩)
  set d := Code.distFromCode (u := f)
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  let e: ℕ := d.toNat
  let k : ℕ := 2^(ℓ - i.val)  -- degree bound from BBF_Code definition
  -- Convert domain to Fin format for Berlekamp-Welch
  let domain_to_fin : (sDomain 𝔽q β h_ℓ_add_R_rate)
    ⟨i, by omega⟩ ≃ Fin domain_size := by
    simp only [domain_size]
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (h_i:=by apply Nat.lt_add_of_pos_right_of_le; simp only; omega), hF₂.out]
    have h_equiv := sDomainFinEquiv 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
      (h_i:=by apply Nat.lt_add_of_pos_right_of_le; simp only; omega)
    convert h_equiv
  -- ωs is the mapping from the point index to the actually point in the domain S^{i}
  let ωs : Fin domain_size → L := fun j => (domain_to_fin.symm j).val
  let f_vals : Fin domain_size → L := fun j => f (domain_to_fin.symm j)
  -- Run Berlekamp-Welch decoder to get P(X) in monomial basis
  have domain_neZero : NeZero domain_size := by
    simp only [domain_size];
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (h_i:=by apply Nat.lt_add_of_pos_right_of_le; simp only; omega)]
    exact {
      out := by
        rw [hF₂.out]
        simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true]
    }
  -- Run Berlekamp-Welch decoder to get P(X) in monomial basis
  let berlekamp_welch_result: Option L[X] := BerlekampWelch.decoder e k ωs f_vals

  match berlekamp_welch_result with
  | none => exact none  -- Decoder failed
  | some P =>
    -- 5. Check if degree < 2^ℓ (unique decoding condition)
    if hp_deg_lt: P.natDegree ≥ 2^(ℓ - i.val) then
      exact none  -- Outside unique decoding radius
    else
      -- 6. Convert P(X) from monomial basis to novel polynomial basis
      -- P(X) = Σᵢ aᵢ Xᵢ (monomial) → P(X) = Σⱼ tⱼ X_{j}(X) (novel)
      -- We need the inverse of the change-of-basis matrix
      have h_deg_bound : P ∈ L[X]_(2^(ℓ - i.val)) := by
        rw [Polynomial.mem_degreeLT]
        by_cases hi: i = ℓ
        · simp only [hi, tsub_self, pow_zero, cast_one]
          by_cases hp_p_eq_0: P = 0
          · simp only [hp_p_eq_0, degree_zero]; omega
          · simp only [hi, tsub_self, pow_zero, ge_iff_le, not_le, lt_one_iff] at hp_deg_lt
            have h_deg_p: P.degree = 0 := by omega
            simp only [h_deg_p]
            omega
        · by_cases hp_p_eq_0: P = 0
          · simp only [hp_p_eq_0];
            have h_i_lt_ℓ : i < ℓ := by omega
            simp only [degree_zero, cast_pow, cast_ofNat, gt_iff_lt]
            -- ⊢ ⊥ < 2 ^ (ℓ - ↑i)
            have h_deg_ne_bot : 2 ^ (ℓ - ↑i) ≠ ⊥ := by
              exact not_isBot_iff_ne_bot.mp fun a ↦ hp_deg_lt (a P.natDegree)
            exact compareOfLessAndEq_eq_lt.mp rfl
          · have h := Polynomial.natDegree_lt_iff_degree_lt (p:=P) (n:=2 ^ (ℓ - ↑i))
              (hp:=by exact hp_p_eq_0)
            rw [←h]; omega
      let P_bounded : L⦃<2^(ℓ - i.val)⦄[X] := ⟨P, h_deg_bound⟩
      -- Get monomial coefficients of P(X)
      let monomial_coeffs : Fin (2^(ℓ - i.val)) → L := fun i => P.coeff i.val
      -- Convert to novel polynomial basis coefficients using change of basis
      -- The changeOfBasisMatrix A has A[j,i] = coeff of X^i in novel basis vector X_j
      -- So we need A⁻¹ to convert monomial coeffs → novel coeffs
      let novel_coeffs : Option (Fin (2^(ℓ - i.val)) → L) :=
        let h_ℓ_le_r : ℓ ≤ r := by
          -- ℓ + 𝓡 < r implies ℓ < r, hence ℓ ≤ r
          have : ℓ < r := by omega
          exact Nat.le_of_lt this
        some (AdditiveNTT.monomialToNovelCoeffs 𝔽q β (ℓ - i.val) (by omega) monomial_coeffs)

      match novel_coeffs with
      | none => exact none
      | some t_coeffs =>
        -- Interpret novel coeffs as Lagrange cosefficients on Boolean hypercube
        -- and reconstruct the multilinear polynomial using MLE
        let hypercube_evals : (Fin (ℓ - i.val) → Fin 2) → L := fun w =>
          -- Map Boolean hypercube point w to its linear index
          let w_index : Fin (2^(ℓ - i.val)) := Nat.binaryFinMapToNat
            (n:=ℓ - i.val) (m:=w) (h_binary:=by intro j; simp only [Nat.cast_id]; omega)
          t_coeffs w_index

        let t_multilinear_mv := MvPolynomial.MLE hypercube_evals
        exact some ⟨t_multilinear_mv, MLE_mem_restrictDegree hypercube_evals⟩

def dummyLastWitness :
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) := {
  t := ⟨0, by apply zero_mem⟩,
  H := ⟨0, by apply zero_mem⟩,
  f := fun _ => 0
}

/-- The initial statement for the commitment phase contains the evaluation claim s = t(r) -/
structure InitialStatement where
  -- Original evaluation claim: s = t(r)
  t_eval_point : Fin ℓ → L         -- r = (r_0, ..., r_{ℓ-1}) => shared input
  original_claim : L               -- s = t(r) => the original claim to verify

section SnocOracleHelpers
/-- Helper lemma: If it is not a commitment round, the oracle count does not increase,
    so an index `j` cannot exist in the range `[old_count, new_count)`. -/
lemma snoc_oracle_impossible {i : Fin ℓ} {j : Fin (toOutCodewordsCount ℓ ϑ i.succ)}
    (hj : ¬ j.val < toOutCodewordsCount ℓ ϑ i.castSucc)
    (h_not_commit : ¬ isCommitmentRound ℓ ϑ i) : False := by
  -- The count relation implies new_count = old_count
  have h_counts_eq : toOutCodewordsCount ℓ ϑ i.succ = toOutCodewordsCount ℓ ϑ i.castSucc := by
    rw [toOutCodewordsCount_succ_eq ℓ ϑ i]
    simp only [h_not_commit, ↓reduceIte]
  -- But j is bounded by new_count
  have h_j_lt_new := j.isLt
  conv_rhs at h_j_lt_new => rw [h_counts_eq]
  -- Contradiction with hj
  exact hj h_j_lt_new

omit [NeZero r] [NeZero 𝓡] in
/-- Helper lemma: If it is a commitment round, the index `j` (which is ≥ old_count)
    must be exactly equal to `old_count`, and consequently its domain index corresponds
    to `destIdx` (which is `i + 1`). -/
lemma snoc_oracle_dest_eq_j {i : Fin ℓ} {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (hj : ¬ j.val < toOutCodewordsCount ℓ ϑ i.castSucc)
    (h_commit : isCommitmentRound ℓ ϑ i) :
    destIdx = ⟨(oraclePositionToDomainIndex ℓ ϑ j).val,
               by have := oraclePositionToDomainIndex ℓ ϑ j; omega⟩ := by
  -- 1. Prove counts relation: new = old + 1
  have h_count_succ : toOutCodewordsCount ℓ ϑ i.succ =
      toOutCodewordsCount ℓ ϑ i.castSucc + 1 := by
    rw [toOutCodewordsCount_succ_eq ℓ ϑ i]
    simp only [h_commit, ↓reduceIte]

  -- 2. Prove j must be exactly old_count
  have h_j_eq : j.val = toOutCodewordsCount ℓ ϑ i.castSucc := by
    have h_lt := j.isLt
    conv_rhs at h_lt => rw [h_count_succ]
    -- j < old + 1 AND NOT j < old  =>  j = old
    omega

  -- 3. Calculate the domain index value for j
  -- We need to prove: destIdx.val = j * ϑ
  apply Fin.eq_of_val_eq
  simp only [h_destIdx, Fin.val_add, Fin.val_one, oraclePositionToDomainIndex]

  -- We know j * ϑ = i + 1 from the structure of commitment rounds
  rw [h_j_eq]
  rw [toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ i h_commit]

open Classical in
/-- snoc_oracle adds the latest oracle function to the end of an oStmtIn -/
def snoc_oracle {i : Fin ℓ} {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx)) :
    ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.succ),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i.succ j := fun j =>
  if hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc then
      -- Case 1: Old oracle (index < old count)
      oStmtIn ⟨j.val, hj⟩
    else
      if hi : isCommitmentRound ℓ ϑ i then
        -- Case 2: New oracle (Commitment round, index == old count)
        -- Derive the equality between the function's expected domain and the actual domain
        let h_eq := snoc_oracle_dest_eq_j (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (ℓ := ℓ) (ϑ := ϑ) h_destIdx j hj hi
        fun x => newOracleFn (cast (by rw [h_eq]) x)
      else
        -- Case 3: Impossible (Not commitment round, but index increased)
        (snoc_oracle_impossible hj hi).elim

def take_snoc_oracle (i : Fin ℓ) {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (oStmtIn : (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx)) :
    (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) → -- We specify range type so Lean won't be stuck
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j
    := fun j => snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) h_destIdx
      oStmtIn newOracleFn ⟨j, by
        have h : (toOutCodewordsCount ℓ ϑ i.castSucc) ≤ toOutCodewordsCount ℓ ϑ i.succ := by
          exact toOutCodewordsCount_i_le_of_succ ℓ ϑ i
        omega
      ⟩

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
lemma take_snoc_oracle_eq_oStmtIn (i : Fin ℓ) {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (oStmtIn : (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx)) :
    (take_snoc_oracle 𝔽q β i h_destIdx oStmtIn newOracleFn) = oStmtIn := by
  unfold take_snoc_oracle snoc_oracle
  if hi: isCommitmentRound ℓ ϑ i then
    simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]
  else
    simp only [Fin.is_lt, ↓reduceDIte, Fin.eta]

end SnocOracleHelpers

/-- Extract the first oracle f^(0) from oracle statements -/
def getFirstOracle {oracleFrontierIdx : Fin (ℓ + 1)}
    (oStmt : (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ oracleFrontierIdx j)) :
    sDomain 𝔽q β h_ℓ_add_R_rate 0 → L := by
  let rawf₀ := oStmt ⟨0, by
    letI := instNeZeroNatToOutCodewordsCount ℓ ϑ oracleFrontierIdx
    exact pos_of_neZero (toOutCodewordsCount ℓ ϑ oracleFrontierIdx)
  ⟩
  simp only [OracleStatement, zero_mul, Fin.mk_zero'] at rawf₀
  exact rawf₀

def getLastOracle {oracleFrontierIdx : Fin (ℓ + 1)} {destIdx : Fin r}
    (h_destIdx : destIdx.val = getLastOracleDomainIndex ℓ ϑ oracleFrontierIdx)
    (oStmt : (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
      (i := oracleFrontierIdx) j)) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx :=
  let res := oStmt ⟨getLastOraclePositionIndex ℓ ϑ oracleFrontierIdx, by omega⟩
  have h_lt : getLastOracleDomainIndex ℓ ϑ oracleFrontierIdx < r := by omega
  have h_eq : destIdx = ⟨getLastOracleDomainIndex ℓ ϑ oracleFrontierIdx, h_lt⟩
    := Fin.eq_of_val_eq (by omega)
  -- subst h_eq
  fun y => res (cast (by rw [h_eq]) y)

section SecurityRelations
/-- Helper to get the challenges for folding.
k is the starting index of the challenge slice. ϑ is the number of steps. -/
def getFoldingChallenges (i : Fin (ℓ + 1)) (challenges : Fin i → L)
    (k : ℕ) (h : k + ϑ ≤ i) : Fin ϑ → L :=
  fun cId => challenges ⟨k + cId, by omega⟩

omit [NeZero r] [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] hdiv in
lemma getFoldingChallenges_init_succ_eq (i : Fin ℓ)
    (j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) (challenges : Fin i.succ → L)
    (h : ↑j * ϑ + ϑ ≤ ↑i.castSucc) :
    getFoldingChallenges (r := r) (𝓡 := 𝓡) (ϑ := ϑ) i.castSucc (Fin.init challenges) (↑j * ϑ)
      (h := by omega) =
    getFoldingChallenges (r := r) (𝓡 := 𝓡) i.succ challenges (↑j * ϑ)
      (h := by simp only [Fin.val_succ]; simp only [Fin.coe_castSucc] at h; omega) := by
  unfold getFoldingChallenges
  ext cId
  simp only [Fin.init, Fin.coe_castSucc, Fin.castSucc_mk, Fin.val_succ]

def getNextOracle (i : Fin (ℓ + 1))
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i) j)
    (j : Fin (toOutCodewordsCount ℓ ϑ i)) (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i)
    {destDomainIdx : Fin r} (h_destDomainIdx : destDomainIdx = j.val * ϑ + ϑ) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destDomainIdx := by
  --   ⟨j.val * ϑ + ϑ, by
  --   apply Nat.lt_succ_of_le;
  --   let h_k_next_le_i := oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i) (j := j) (hj := hj)
  --   calc _ ≤ i.val := h_k_next_le_i
  --     _ ≤ ℓ := Fin.is_le i
  -- ⟩ := by
    let res := oStmt ⟨j.val + 1, hj⟩
    have h: j.val * ϑ + ϑ = (j.val + 1) * ϑ := by
      rw [Nat.add_mul, one_mul]
    dsimp only [OracleStatement] at res
    have h_lt : (↑j + 1) * ϑ < r := by omega
    have h_eq : destDomainIdx = ⟨(↑j + 1) * ϑ, h_lt⟩ := Fin.eq_of_val_eq (by simp only; omega)
    subst h_eq
    -- rw! [h]
    exact res

/-- Folding consistency for round i (where i is the oracleIdx) -/
def oracleFoldingConsistencyProp (i : Fin (ℓ + 1)) (challenges : Fin i → L)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i) j)
    (includeFinalFiberwiseClose : Bool) : Prop :=
    -- TODO: check index of this
  (∀ (j : Fin (toOutCodewordsCount ℓ ϑ i)) (hj : j.val + 1 < toOutCodewordsCount ℓ ϑ i),
    -- let k is j.val * ϑ
    have h_k_bound := oracle_block_k_bound (ℓ := ℓ) (ϑ := ϑ) (i := i) (j := j)
    have h_k_next_le_i := oracle_block_k_next_le_i (ℓ := ℓ) (ϑ := ϑ) (i := i) (j := j) (hj := hj)
    let destIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j) + ϑ, by
      have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i) (j := j)
      dsimp only [oraclePositionToDomainIndex]
      omega
    ⟩
    -- Explicitly type the oracle functions
    isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩) (steps := ϑ)
      (destIdx := destIdx) (by rfl) (by dsimp only [destIdx]; simp only [oracle_index_add_steps_le_ℓ])
      (f_i := oStmt ⟨j.val, by exact j.isLt⟩)
      (f_i_plus_steps := getNextOracle 𝔽q β i oStmt j hj (destDomainIdx := destIdx) (h_destDomainIdx := by rfl))
      (challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) i challenges (k := j.val * ϑ)
        (h := h_k_next_le_i))
  )
  ∧
  (if includeFinalFiberwiseClose then
    -- the last oracle is fiberwise-close to its code
    let curDomainIdx : Fin r := ⟨getLastOracleDomainIndex ℓ ϑ i, by omega⟩
    let destDomainIdx : Fin r := ⟨getLastOracleDomainIndex ℓ ϑ i + ϑ, by
      have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := i) (j := getLastOraclePositionIndex ℓ ϑ i)
      dsimp only [oraclePositionToDomainIndex]
      omega
    ⟩
    fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := curDomainIdx) (steps := ϑ)
      (destIdx := destDomainIdx) (by rfl) (by dsimp only [destDomainIdx]; simp only [oracle_index_add_steps_le_ℓ])
      (f := getLastOracle (h_destIdx := by rfl)
        (oracleFrontierIdx := i) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmt))
  else True)

def BBF_eq_multiplier (r : Fin ℓ → L) : MultilinearPoly L ℓ :=
  ⟨MvPolynomial.eqPolynomial r, by simp only [eqPolynomial_mem_restrictDegree]⟩

def BBF_SumcheckMultiplierParam : SumcheckMultiplierParam L ℓ (SumcheckBaseContext L ℓ) :=
  { multpoly := fun ctx => BBF_eq_multiplier ctx.t_eval_point }

/-- This condition ensures that the folding witness `f` is properly generated from `t` -/
def getMidCodewords {i : Fin (ℓ + 1)} (t : L⦃≤ 1⦄[X Fin ℓ]) -- original polynomial t
    (challenges : Fin i → L) : (sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) → L) :=
  let P₀ : L⦃< 2^ℓ⦄[X] := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (h_ℓ := by omega)
    (a := fun ω => t.val.eval (bitsOfIndex ω))
    -- NOTE: must be `bitsOfIndex ω` to get a function of values in `𝓑`
  let f₀ : (sDomain 𝔽q β h_ℓ_add_R_rate 0) → L := fun x => P₀.val.eval x.val
  let fᵢ := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := 0) (steps := i) (destIdx := ⟨i, by omega⟩) (h_destIdx := by simp only [Fin.coe_ofNat_eq_mod,
      zero_mod, zero_add]) (h_destIdx_le := by simp only; omega)
    (f := f₀)
    (r_challenges := challenges)
  fun x => fᵢ x

-- TODO: double check this?
lemma getMidCodewords_succ (t : L⦃≤ 1⦄[X Fin ℓ]) (i : Fin ℓ)
    (challenges : Fin i.castSucc → L) (r_i' : L) :
    (getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i.succ) (t := t) (challenges := Fin.snoc challenges r_i')) =
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := 1)
      (destIdx := ⟨i.succ, by omega⟩) (h_destIdx := by simp only [Fin.val_succ])
      (h_destIdx_le := by simp only; omega)
      (f := getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i.castSucc)
      (t := t) (challenges := challenges)) (r_challenges := fun _ => r_i'))
    := by
  sorry

section FoldStepLogic
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

def foldPrvState (i : Fin ℓ) : Fin (2 + 1) → Type := fun
  -- Initial : current  witness x t_eval_point x challenges
  | ⟨0, _⟩ => (Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
  -- After sending h_i(X)
  | ⟨1, _⟩ => Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc × L⦃≤ 2⦄[X]
  -- After receiving r'_i (Note that this covers the last two messages, i.e. after each of them)
  | _ => Statement (L := L) Context i.castSucc ×
    (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) ×
    Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc × L⦃≤ 2⦄[X] × L

/-- This is in fact usable immediately after the V->P challenge since all inputs
are available at that time. -/
@[reducible]
noncomputable def getFoldProverFinalOutput (i : Fin ℓ)
    (finalPrvState : foldPrvState 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i 2 (Context := Context)) :
  ((Statement (L := L) Context i.succ × ((j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) →
    OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j))
      × Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
  := by
  let (stmtIn, oStmtIn, witIn, h_i, r_i') := finalPrvState
  let newSumcheckTarget : L := h_i.val.eval r_i'
  let stmtOut : Statement (L := L) Context i.succ := {
    ctx := stmtIn.ctx,
    sumcheck_target := newSumcheckTarget,
    challenges := Fin.snoc stmtIn.challenges r_i'
  }
  let currentSumcheckPoly : L⦃≤ 2⦄[X Fin (ℓ - i)] := witIn.H
  let f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (domainIdx := ⟨i, by omega⟩) := witIn.f
  let challenges : Fin (1) → L := fun cId => r_i'
  let fᵢ_succ := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (steps := 1) (destIdx := ⟨i.succ, by omega⟩) (h_destIdx := by simp only [Fin.val_succ]) (h_destIdx_le := by simp only; omega)
    f_i challenges
  simp only at fᵢ_succ
  let witOut : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ℓ := ℓ) i.succ := by
    -- Advance Hᵢ → Hᵢ₊₁ by fixing the first variable to rᵢ'
    let projectedH := projectToNextSumcheckPoly (L := L) (ℓ := ℓ)
      (i := i) (Hᵢ := witIn.H) (rᵢ := r_i')
    exact {
      t := witIn.t,
      H := projectedH,
      f := fᵢ_succ
    }
  have h_succ_val : i.succ.val = i.val + 1 := rfl
  let oStmtOut : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc j := oStmtIn
  exact ⟨⟨stmtOut, oStmtOut⟩, witOut⟩

/-- Atomic Logic: Computes the Sumcheck polynomial h_i(X) from the current witness. -/
@[reducible]
def foldProverComputeMsg (i : Fin ℓ)
    (witIn : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc) :
    L⦃≤ 2⦄[X] :=
  getSumcheckRoundPoly ℓ 𝓑 (i := i) witIn.H

/-- Pure verifier check extracted from foldOracleVerifier.verify (line 166).
For fold step: sumcheck condition must hold. -/
@[reducible]
def foldVerifierCheck (i : Fin ℓ)
    (stmtIn : Statement (L := L) Context i.castSucc)
    (msg0 : L⦃≤ 2⦄[X]) : Prop :=
  msg0.val.eval (𝓑 0) + msg0.val.eval (𝓑 1) = stmtIn.sumcheck_target

/-- Pure verifier output computation extracted from foldOracleVerifier.verify (lines 180-184).
What verifier returns after checks pass. -/
@[reducible]
def foldVerifierStmtOut (i : Fin ℓ)
    (stmtIn : Statement (L := L) Context i.castSucc)
    (msg0 : L⦃≤ 2⦄[X])
    (chal1 : L) :
    Statement (L := L) Context i.succ :=
  {
    ctx := stmtIn.ctx,
    sumcheck_target := msg0.val.eval chal1,
    challenges := Fin.snoc stmtIn.challenges chal1
  }

end FoldStepLogic

/-! `SumcheckContextIncluded_Relations`: Sumcheck context is passed as a
parameters in the following relations --/
section SumcheckContextIncluded_Relations
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context

/-- This condition ensures that the witness polynomial `H` has the
correct structure `eq(...) * t(...)`. At the commitment steps (in commitment rounds),
wit.f is exactly the same as the last oracle being sent. -/
def witnessStructuralInvariant {i : Fin (ℓ + 1)} (stmt : Statement (L := L) Context i)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  wit.H = projectToMidSumcheckPoly ℓ wit.t (m:=mp.multpoly stmt.ctx) i stmt.challenges ∧
  wit.f = getMidCodewords 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) wit.t stmt.challenges

/-- Sumcheck consistency: the claimed sum equals the actual polynomial evaluation sum -/
def sumcheckConsistencyProp {k : ℕ} (sumcheckTarget : L) (H : L⦃≤ 2⦄[X Fin (k)]) : Prop :=
  sumcheckTarget = ∑ x ∈ (univ.map 𝓑) ^ᶠ (k), H.val.eval x

/-- First oracle witness consistency: the witness polynomial t, when projected to level 0 and
    evaluated on the initial domain S^(0), must be close within unique decoding radius to f^(0) -/
def firstOracleWitnessConsistencyProp (t : MultilinearPoly L ℓ)
    (f₀ : sDomain 𝔽q β h_ℓ_add_R_rate 0 → L) : Prop :=
  let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) (fun ω => t.val.eval (bitsOfIndex ω))
  -- The constraint: P_0 evaluated on S^(0) is close within unique decoding radius to f^(0)
  pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := 0) (h_i := by
    simp only [Fin.coe_ofNat_eq_mod, zero_mod, _root_.zero_le]) (f := f₀)
    (g := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀))

/-- The bad folding event of `fᵢ` exists RIGHT AFTER the V's challenge of sumcheck round `i+ϑ-1`,
this is the last point that `fᵢ` is the last oracle being sent so far and both
Statement & Witness are advanced to state `i+ϑ`, while oracle is still at state `i+ϑ-1`.
-/
noncomputable def foldingBadEventAtBlock
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (i := oracleIdx.val) j)) (challenges : Fin stmtIdx → L)
    (j : Fin (toOutCodewordsCount ℓ ϑ oracleIdx.val)) : Prop :=
  have h_ϑ: ϑ > 0 := by exact pos_of_neZero ϑ
  -- TODO: check this
  let curOracleDomainIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by omega⟩
  if hj: curOracleDomainIdx + ϑ ≤ oracleIdx.val then
    let f_k := oStmt j
    let destIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j) + ϑ, by
      have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := oracleIdx.val) (j := j)
      dsimp only [oraclePositionToDomainIndex]
      omega
    ⟩
    Binius.BinaryBasefold.foldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := curOracleDomainIdx) (steps := ϑ) (destIdx := destIdx) (by rfl) (by dsimp only [destIdx]; simp only [oracle_index_add_steps_le_ℓ]) (f_i := f_k) (r_challenges :=
        getFoldingChallenges (r := r) (𝓡 := 𝓡) stmtIdx challenges (k := j.val * ϑ) (h := by
        have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := oracleIdx.val) (j := j)
        simp only [curOracleDomainIdx] at hj
        have h := OracleFrontierIndex.val_le_i (i := stmtIdx) (oracleIdx := oracleIdx)
        exact Nat.le_trans hj h
      ))
  else False

attribute [irreducible] foldingBadEventAtBlock

open Classical in
def badEventExistsProp
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ)
      (i := oracleIdx.val) j)) (challenges : Fin stmtIdx → L) : Prop :=
  ∃ j, foldingBadEventAtBlock 𝔽q β (stmtIdx := stmtIdx) (oracleIdx := oracleIdx)
    (oStmt := oStmt) (challenges := challenges) j

def oracleWitnessConsistency
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (stmt : Statement (L := L) (Context := Context) stmtIdx)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (i := oracleIdx.val) j)) : Prop :=
  let witnessStructuralInvariant: Prop := witnessStructuralInvariant (i:=stmtIdx) 𝔽q β (mp := mp)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit
  let firstOracleConsistency: Prop := firstOracleWitnessConsistencyProp 𝔽q β
    wit.t (getFirstOracle 𝔽q β oStmt)
  let oracleFoldingConsistency: Prop := oracleFoldingConsistencyProp 𝔽q β (i := oracleIdx.val)
    (challenges := Fin.take (m := oracleIdx.val) (v := stmt.challenges)
    (h := by simp only [Fin.val_fin_le, OracleFrontierIndex.val_le_i]))
    (oStmt := oStmt) (includeFinalFiberwiseClose := true)
  witnessStructuralInvariant ∧ firstOracleConsistency ∧
    oracleFoldingConsistency

section SingleStepRelationPreservationLemmas

-- lemma nonDoomedFoldingProp_relay_preserved (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
--     (challenges : Fin i.succ → L)
--     (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
--     :
--     nonDoomedFoldingProp 𝔽q β i.castSucc (Fin.init challenges) oStmt ↔
--     nonDoomedFoldingProp 𝔽q β i.succ challenges (mapOStmtOutRelayStep 𝔽q β i hNCR oStmt) := by
--   have h_oracle_size_eq: toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ := by
--     simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hNCR, ↓reduceIte]
--   unfold nonDoomedFoldingProp
--   -- Both sides are of the form (oracleFoldingConsistency ∨ foldingBadEventExists)
--   -- Since mapOStmtOutRelayStep just reindexes with the same oracle count, both properties are preserved
--   constructor
--   · intro h
--     cases h with
--     | inl h_folding =>
--       left
--       unfold oracleFoldingConsistencyProp at h_folding ⊢
--       intro j hj
--       -- Map j back to the original index
--       have h_j_mapped : j.val < toOutCodewordsCount ℓ ϑ i.castSucc := by omega
--       let j_orig : Fin (toOutCodewordsCount ℓ ϑ i.castSucc) := ⟨j.val, h_j_mapped⟩
--       have hj_orig : j_orig.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc := by simp [j_orig]; omega
--       have h_spec := h_folding j_orig hj_orig
--       unfold mapOStmtOutRelayStep getNextOracle
--       simp only [h_oracle_size_eq]
--       -- The oracle functions and challenges are the same, just reindexed
--       simp only [Fin.eta] at h_spec
--       sorry
--     | inr h_bad =>
--       right
--       unfold badEventExistsProp at h_bad ⊢
--       sorry
--       -- obtain ⟨j, hj, h_bad_event⟩ := h_bad
--       -- use ⟨j.val, by omega⟩
--       -- constructor
--       -- · omega
--       -- · unfold mapOStmtOutRelayStep getNextOracle foldingBadEventAtBlock
--       --   simp only [h_oracle_size_eq]
--       --   convert h_bad_event using 2
--       --   · unfold getFoldingChallenges
--       --     ext cId
--       --     simp only [Fin.init, Fin.coe_castSucc, Fin.castSucc_mk, Fin.val_succ]
--       --   · rfl
--       --   · rfl
--   · intro h
--     cases h with
--     | inl h_folding =>
--       left
--       unfold oracleFoldingConsistencyProp at h_folding ⊢
--       intro j hj
--       -- Map j forward to the new index
--       let j_new : Fin (toOutCodewordsCount ℓ ϑ i.succ) := ⟨j.val, by omega⟩
--       have hj_new : j_new.val + 1 < toOutCodewordsCount ℓ ϑ i.succ := by simp [j_new]; omega
--       have h_spec := h_folding j_new hj_new
--       unfold mapOStmtOutRelayStep getNextOracle at h_spec
--       simp only [h_oracle_size_eq] at h_spec
--       sorry
--       -- convert h_spec using 2
--       -- · unfold getFoldingChallenges
--       --   ext cId
--       --   simp only [Fin.init, Fin.coe_castSucc, Fin.castSucc_mk, Fin.val_succ]
--       -- · rfl
--       -- · rfl
--     | inr h_bad =>
--       right
--       unfold badEventExistsProp at h_bad ⊢
--       sorry
--       -- obtain ⟨j, hj, h_bad_event⟩ := h_bad
--       -- use ⟨j.val, by omega⟩
--       -- constructor
--       -- · omega
--       -- · unfold mapOStmtOutRelayStep getNextOracle foldingBadEventAtBlock at h_bad_event
--       --   simp only [h_oracle_size_eq] at h_bad_event
--       --   convert h_bad_event using 2
--       --   · unfold getFoldingChallenges
--       --     ext cId
--       --     simp only [Fin.init, Fin.coe_castSucc, Fin.castSucc_mk, Fin.val_succ]
--       --   · rfl
--       --   · rfl

-- lemma badEventExistsProp_succ_preserved (i : Fin ℓ) (oStmtIn : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) (stmtIn : Statement (L := L) Context i.castSucc)  (r_i': L) (h_badEvent_In :
--   badEventExistsProp 𝔽q β i.castSucc (OracleFrontierIndex.mkFromStmtIdx i.castSucc) oStmtIn stmtIn.challenges) :
--   badEventExistsProp 𝔽q β i.succ (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i) oStmtIn
--     (Fin.snoc stmtIn.challenges r_i') := by
--   obtain ⟨j , hj⟩ := h_badEvent_In
--   dsimp only [Fin.val_succ, badEventExistsProp,
--     OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc] at hj ⊢
--   use j
--   simp only  [foldingBadEventAtBlock] at hj ⊢
--         -- rw! (castMode := .all) [←OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc_eq_mkFromStmtIdx (i := i)] at h_badEvent_In
--   -- rw! (castMode := .all) [←OracleFrontierIndex.val_mkFromStmtIdxCastSuccOfSucc_eq_mkFromStmtIdx (i := i)] at h_badEvent_In
--   sorry

/-- Oracle embedding for commit step: maps existing oracles via Sum.inl,
and the new oracle to Sum.inr ⟨0, rfl⟩ -/
def commitStepEmbed (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    Fin (toOutCodewordsCount ℓ ϑ i.succ) ↪
    (Fin (toOutCodewordsCount ℓ ϑ i.castSucc) ⊕ Fin 1) := ⟨fun j => by
  classical
  if hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc then
    exact Sum.inl ⟨j.val, by omega⟩
  else
    exact Sum.inr ⟨0, by omega⟩
, by
  intro a b h_ab_eq
  simp only [MessageIdx, Fin.isValue] at h_ab_eq
  split_ifs at h_ab_eq with h_ab_eq_l h_ab_eq_r
  · simp at h_ab_eq; apply Fin.eq_of_val_eq; exact h_ab_eq
  · have ha_lt : a < toOutCodewordsCount ℓ ϑ i.succ := by omega
    have hb_lt : b < toOutCodewordsCount ℓ ϑ i.succ := by omega
    conv_rhs at ha_lt => rw [toOutCodewordsCount_succ_eq ℓ ϑ i]
    conv_rhs at hb_lt => rw [toOutCodewordsCount_succ_eq ℓ ϑ i]
    simp only [hCR, ↓reduceIte] at ha_lt hb_lt
    have h_a : a = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
    have h_b : b = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
    omega
⟩

/-- Oracle statement type equality for commit step -/
def commitStepHEq (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    ∀ (oracleIdx : Fin (toOutCodewordsCount ℓ ϑ i.succ)),
    OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ oracleIdx =
    match commitStepEmbed (r := r) (𝓡 := 𝓡) i hCR oracleIdx with
    | Sum.inl j => OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j
    | Sum.inr _ => sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.succ, by omega⟩ → L := fun oracleIdx => by
  unfold OracleStatement commitStepEmbed
  simp only [MessageIdx, Fin.isValue, Function.Embedding.coeFn_mk]
  by_cases hlt : oracleIdx.val < toOutCodewordsCount ℓ ϑ i.castSucc
  · simp only [hlt, ↓reduceDIte]
  · simp only [hlt, ↓reduceDIte, Fin.isValue]
    have hOracleIdx_lt : oracleIdx.val < toOutCodewordsCount ℓ ϑ i.succ := by omega
    simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hCR, ↓reduceIte] at hOracleIdx_lt
    have hOracleIdx : oracleIdx = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
    simp_rw [hOracleIdx]
    have h := toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ (i := i) (hCR := hCR)
    rw! [h]; rfl

section FoldStepPreservationLemmas
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context}

end FoldStepPreservationLemmas

lemma oracleWitnessConsistency_relay_preserved
    (i : Fin ℓ) (hNCR : ¬ isCommitmentRound ℓ ϑ i)
    (stmt : Statement (L := L) Context i.succ)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j) :
    oracleWitnessConsistency 𝔽q β (mp := mp) i.succ
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i) stmt wit oStmt =
    oracleWitnessConsistency 𝔽q β (mp := mp) i.succ
      (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i.succ) stmt wit
      (mapOStmtOutRelayStep 𝔽q β i hNCR oStmt) := by
  unfold oracleWitnessConsistency
  -- All four components (witnessStructuralInvariant, sumCheckConsistency,
  -- firstOracleConsistency, oracleFoldingConsistency) are preserved during relay
  have h_oracle_size_eq: toOutCodewordsCount ℓ ϑ i.castSucc = toOutCodewordsCount ℓ ϑ i.succ := by
    simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hNCR, ↓reduceIte]

  congr 1
  sorry
  -- -- firstOracleConsistency: getFirstOracle is preserved
  -- · unfold getFirstOracle
  --   simp only [mapOStmtOutRelayStep, h_oracle_size_eq]
  -- -- oracleFoldingConsistency: preserved by similar reasoning to nonDoomedFoldingProp_relay_preserved
  -- · unfold oracleFoldingConsistencyProp
  --   apply propext
  --   constructor <;> intro h j hj
  --   · -- Forward direction
  --     have h_j_mapped : j.val < toOutCodewordsCount ℓ ϑ i.castSucc := by omega
  --     let j_orig : Fin (toOutCodewordsCount ℓ ϑ i.castSucc) := ⟨j.val, h_j_mapped⟩
  --     have hj_orig : j_orig.val + 1 < toOutCodewordsCount ℓ ϑ i.castSucc := by simp [j_orig]; omega
  --     have h_spec := h j_orig hj_orig
  --     unfold mapOStmtOutRelayStep getNextOracle
  --     simp only [h_oracle_size_eq]
  --     convert h_spec using 2
  --     · unfold getFoldingChallenges; ext cId
  --       have h_take_init : Fin.take (m := i.succ) (h := by omega) stmt.challenges =
  --         Fin.init stmt.challenges := by
  --         ext k; simp [Fin.take, Fin.init]
  --       rw [h_take_init]
  --       simp [Fin.init, Fin.coe_castSucc, Fin.castSucc_mk, Fin.val_succ]
  --     · rfl
  --     · rfl
  --   · -- Backward direction
  --     let j_new : Fin (toOutCodewordsCount ℓ ϑ i.succ) := ⟨j.val, by omega⟩
  --     have hj_new : j_new.val + 1 < toOutCodewordsCount ℓ ϑ i.succ := by simp [j_new]; omega
  --     have h_spec := h j_new hj_new
  --     unfold mapOStmtOutRelayStep getNextOracle at h_spec
  --     simp only [h_oracle_size_eq] at h_spec
  --     convert h_spec using 2
  --     · unfold getFoldingChallenges; ext cId
  --       have h_take_init : Fin.take (m := i.succ) (h := by omega) stmt.challenges =
  --         Fin.init stmt.challenges := by
  --         ext k; simp [Fin.take, Fin.init]
  --       rw [h_take_init]
  --       simp [Fin.init, Fin.coe_castSucc, Fin.castSucc_mk, Fin.val_succ]
  --     · rfl
  --     · rfl

end SingleStepRelationPreservationLemmas
/-- Before V's challenge of the `i-th` foldStep, we ignore the bad-folding-event
of the `i-th` oracle if any and enable it after the next V's challenge, i.e. one
round later. This is for the purpose of reasoning its RBR KS properly.

When `includeBadEvents = true` (RBR KS): `localChecks ∧ (badEvent ∨ oracleConsistency)`
When `includeBadEvents = false` (Completeness): `localChecks ∧ oracleConsistency`
-/
def masterKStateProp (stmtIdx : Fin (ℓ + 1))
    (oracleIdx : OracleFrontierIndex stmtIdx)
    (stmt : Statement (L := L) Context stmtIdx)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ
      (i := oracleIdx.val) j))
    (localChecks : Prop := True) (includeBadEvents : Bool) : Prop :=
  let oracleWitnessConsistency: Prop := oracleWitnessConsistency 𝔽q β (mp := mp)
    stmtIdx oracleIdx stmt wit oStmt
  let badEventExists := badEventExistsProp 𝔽q β stmtIdx oracleIdx
    (challenges := stmt.challenges) (oStmt := oStmt)
  let core := if includeBadEvents then badEventExists ∨ oracleWitnessConsistency
              else oracleWitnessConsistency
  localChecks ∧ core

def roundRelationProp (i : Fin (ℓ + 1))
    (input : (Statement (L := L) Context i ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (includeBadEvents : Bool) : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmt.sumcheck_target wit.H
  masterKStateProp (mp := mp) 𝔽q β
    (stmtIdx := i) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i) stmt wit oStmt
    (localChecks := sumCheckConsistency) (includeBadEvents := includeBadEvents)

/-- A modified version of roundRelationProp (i+1) -/
def foldStepRelOutProp (i : Fin ℓ)
    (input : (Statement (L := L) Context i.succ ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
    (includeBadEvents : Bool) : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmt.sumcheck_target wit.H
  masterKStateProp (mp := mp) 𝔽q β
    (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
    stmt wit oStmt
      (localChecks := sumCheckConsistency) (includeBadEvents := includeBadEvents)

/-- This is a special case of nonDoomedFoldingProp for `i = ℓ`, where we support
the consistency between the last oracle `ℓ - ϑ` and the final constant `c`.
This definition has form similar to masterKState where there is no localChecks.

When `includeBadEvents = true` (RBR KS): `oracleFoldingConsistency ∨ badEventExists`
When `includeBadEvents = false` (Completeness): `oracleFoldingConsistency`
-/
def finalFoldingStateProp {h_le : ϑ ≤ ℓ}
    (input : (FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)))
    (includeBadEvents : Bool) :
    Prop :=
  let stmt := input.1
  let oStmt := input.2
  -- let f_ℓ: (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨ℓ, by omega⟩ → L := fun x => stmt.final_constant
  let j := getLastOraclePositionIndex (ℓ := ℓ) (ϑ := ϑ) (Fin.last ℓ) -- actually `j = ℓ / ϑ - 1`
  let k := j.val * ϑ -- k = getLastOracleDomainIndex (Fin.last ℓ)
  have h_k: k = ℓ - ϑ := by
    dsimp only [k, j]
    rw [getLastOraclePositionIndex_last]
    rw [Nat.sub_mul, Nat.one_mul]
    rw [Nat.div_mul_cancel (hdiv.out)]
  let f_k := oStmt j
  let challenges : Fin ϑ → L := fun cId => stmt.challenges ⟨k + cId, by
    simp only [Fin.val_last, k, j]
    rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
    rw [Nat.sub_add_eq_sub_sub_rev (h1:=by omega) (h2:=by omega)]; omega
  ⟩
  have h_k_add_ϑ: k + ϑ = ℓ := by rw [h_k]; apply Nat.sub_add_cancel; omega
  let finalOracleFoldingConsistency: Prop := by
    -- folding consistency between two adjacent oracles `j` & `j + ϑ`
    exact isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨k, by omega⟩) (steps := ϑ) (destIdx := ⟨k + ϑ, by omega⟩) (by rfl) (by simp only; omega) (f_i := f_k)
      (f_i_plus_steps := fun x => stmt.final_constant) (challenges := challenges)

  -- If oracleFoldingConsistency is true, then we can extract the original
    -- well-formed poly `t` and derive witnesses that satisfy the relations at any state
  let oracleFoldingConsistency: Prop :=
    (oracleFoldingConsistencyProp 𝔽q β (i := Fin.last ℓ)
      (challenges := stmt.challenges) (oStmt := oStmt) (includeFinalFiberwiseClose := false)) -- Note: we ignore the fiberwise-closeness of last oracle since it's
                    -- available in finalOracleFoldingConsistency
    ∧ finalOracleFoldingConsistency

  let finalFoldingBadEvent : Prop :=
    Binius.BinaryBasefold.foldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨k, by omega⟩) (steps := ϑ) (destIdx := ⟨k + ϑ, by omega⟩) (by rfl) (by simp only; omega) (f_i := f_k)
      (r_challenges := challenges)

  -- All bad folding events are fully formed across the sum-check rounds,
    -- no new bad event at the final sumcheck step
  let foldingBadEventExists : Prop := (badEventExistsProp 𝔽q β (stmtIdx := Fin.last ℓ)
    (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
    (oStmt := oStmt) (challenges := stmt.challenges)) ∨ finalFoldingBadEvent

  if includeBadEvents then oracleFoldingConsistency ∨ foldingBadEventExists
  else oracleFoldingConsistency

/-- **Relaxed fold step output relation for RBR Knowledge Soundness**.

This is a proximity-based relation used for RBR KS. For completeness proofs, use
`strictFoldStepRelOut` (defined below) instead.

Input relation for round i: R_i must hold at the beginning of round i -/
def foldStepRelOut (i : Fin ℓ) (includeBadEvents : Bool) :
    Set ((Statement (L := L) Context i.succ ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :=
  { input | foldStepRelOutProp (mp := mp) (𝓑 := 𝓑) 𝔽q β i input includeBadEvents}

/-- **Relaxed round relation for RBR Knowledge Soundness**.

This relation uses **proximity-based checks** to track whether a prover's state is "doomed"
(far from any valid codeword) or could potentially be close to a valid witness.

**Important**: This relation is used **only** for RBR Knowledge Soundness proofs.
For Perfect Completeness proofs, use `strictRoundRelation` (defined below) instead.

Relation at step `i` of the CoreInteraction. `∀ i < ℓ, R_i` must hold at the
beginning of ITERATION `i`. `R_ℓ` must hold after the last iteration and before sending
the final constant.

Parameters:
- `includeBadEvents = true`: Track bad folding events (for soundness analysis)
- `includeBadEvents = false`: Ignore bad events (for completeness with relaxed checks)
  **Note**: Even with `false`, this is still a proximity-based relation, not strict equality!
-/
def roundRelation (i : Fin (ℓ + 1)) (includeBadEvents : Bool) :
    Set ((Statement (L := L) Context i ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  { input | roundRelationProp (mp := mp) (𝓑 := 𝓑) 𝔽q β i input includeBadEvents}

/-- Relation for final sumcheck step -/
def finalSumcheckRelOutProp
    (input : ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
      (Unit)))
    (includeBadEvents : Bool) : Prop :=
  -- Final oracle consistency and bad events
  finalFoldingStateProp 𝔽q β
    (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
    (input := input.1)
    (includeBadEvents := includeBadEvents)

/-- **Relaxed final sumcheck relation for RBR Knowledge Soundness**.

This is a proximity-based relation used for RBR KS. For completeness proofs, use
`strictFinalSumcheckRelOut` (defined below) instead. -/
def finalSumcheckRelOut (includeBadEvents : Bool) :
    Set ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
      (Unit)) :=
  { input | finalSumcheckRelOutProp 𝔽q β input includeBadEvents }

/-!
## Strict Completeness Relations (Dual-Relations Framework - Left Column)

These relations use **exact algebraic equality** instead of proximity measures.
They are used **only** for Perfect Completeness proofs (probability 1).

**Key Differences from Relaxed Relations:**
- No bad events tracking
- No proximity checks (`pair_UDRClose`, `fiberwiseClose`, `isCompliant`)
- Only exact equality (`=`) and exact code membership (`∈`)
- Deterministic preservation (probability 1)

See `dualRelation.md` for the theoretical justification of this separation.
-/

/-- **Strict folding consistency for round i** (for Completeness).

This directly checks that each oracle function equals the expected codeword computed from `t`
via `iterated_fold`. This is simpler and more direct than checking code membership and folding
consistency separately, since the honest prover constructs oracles exactly this way.

For each oracle at position `j` with domain index `sourceIdx = j * ϑ`, we require:
  `oStmt j = getMidCodewords t (challenges restricted to sourceIdx)`

This ensures deterministic preservation with probability 1 and
makes completeness proofs straightforward. -/
def strictOracleFoldingConsistencyProp (t : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
    (challenges : Fin i → L)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i) j) : Prop :=
  let P₀: L[X]_(2 ^ ℓ) := polynomialFromNovelCoeffsF₂ 𝔽q β ℓ (by omega) (fun ω => t.val.eval (bitsOfIndex ω))
  let f₀ := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := 0) (P := P₀)
  ∀ (j : Fin (toOutCodewordsCount ℓ ϑ i)),
    -- The constraint: fⱼ is exactly equal to the folded function of the
      -- evaluations of P₀ over S⁽⁰⁾
    let destIdx : Fin r := ⟨oraclePositionToDomainIndex (positionIdx := j), by
      have h_le := oracle_index_le_ℓ (i := i) (j := j); omega
    ⟩
    have h_k_next_le_i := oracle_block_k_le_i (i := i) (j := j);
    let fⱼ : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := oStmt j
    let folded_func := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := j * ϑ) (destIdx := destIdx) (h_destIdx := by
        dsimp only [Fin.coe_ofNat_eq_mod, destIdx]; simp only [zero_mod, zero_add])
      (h_destIdx_le := by have h_le := oracle_index_le_ℓ (i := i) (j := j); omega)
      (f := f₀) (r_challenges := getFoldingChallenges (r := r) (𝓡 := 𝓡) i
        challenges (k := 0) (ϑ := j * ϑ) (h := by omega))
    fⱼ = folded_func

/-- **Strict oracle-witness consistency** (for Completeness).

This combines all strict consistency checks without any proximity measures or bad events.
Used only for Perfect Completeness proofs.

The consistency check is straightforward: each oracle must equal the expected codeword
computed from `wit.t` via `iterated_fold`. This directly captures how the honest prover
constructs oracles, making completeness proofs simple. -/
def strictOracleWitnessConsistency
    (stmtIdx : Fin (ℓ + 1)) (oracleIdx : OracleFrontierIndex stmtIdx)
    (stmt : Statement (L := L) (Context := Context) stmtIdx)
    (wit : Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmtIdx)
    (oStmt : ∀ j, (OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ϑ (i := oracleIdx.val) j)) : Prop :=
  let witnessStructuralInvariant: Prop := witnessStructuralInvariant (i:=stmtIdx) 𝔽q β (mp := mp)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) stmt wit
  let strictOracleFoldingConsistency: Prop := strictOracleFoldingConsistencyProp 𝔽q β
    (t := wit.t) (i := oracleIdx.val)
    (challenges := Fin.take (m := oracleIdx.val) (v := stmt.challenges)
    (h := by simp only [Fin.val_fin_le, OracleFrontierIndex.val_le_i]))
    (oStmt := oStmt)
  witnessStructuralInvariant ∧ strictOracleFoldingConsistency

/-- **Strict round relation property** (for Completeness).

This is the strict version of `roundRelationProp` that uses exact equality checks.
Used only for Perfect Completeness proofs. -/
def strictRoundRelationProp (i : Fin (ℓ + 1))
    (input : (Statement (L := L) Context i ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmt.sumcheck_target wit.H
  let strictOracleWitnessConsistency: Prop := strictOracleWitnessConsistency 𝔽q β (mp := mp)
    (stmtIdx := i) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx i) stmt wit oStmt
  sumCheckConsistency ∧ strictOracleWitnessConsistency

/-- **Strict fold step output relation property** (for Completeness).

This is the strict version of `foldStepRelOutProp` that uses exact equality checks.
Used only for Perfect Completeness proofs. -/
def strictFoldStepRelOutProp (i : Fin ℓ)
    (input : (Statement (L := L) Context i.succ ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) : Prop :=
  let stmt := input.1.1
  let oStmt := input.1.2
  let wit := input.2
  let sumCheckConsistency: Prop := sumcheckConsistencyProp (𝓑 := 𝓑) stmt.sumcheck_target wit.H
  let strictOracleWitnessConsistency: Prop := strictOracleWitnessConsistency 𝔽q β (mp := mp)
    (stmtIdx := i.succ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i)
    stmt wit oStmt
  sumCheckConsistency ∧ strictOracleWitnessConsistency

/-- **Strict final folding state property** (for Completeness).

This is the strict version of `finalFoldingStateProp` that:
- Removes all bad event tracking
- Uses exact code membership and equality instead of proximity-based checks
- Ensures deterministic preservation with probability 1

Used only for Perfect Completeness proofs. -/
def strictFinalFoldingStateProp (t : MultilinearPoly L ℓ) {h_le : ϑ ≤ ℓ}
    (input : (FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j))) :
    Prop :=
  let stmt := input.1
  let oStmt := input.2
  -- All oracle folding consistency (including last oracle)
  let strictOracleFoldingConsistency: Prop :=
    strictOracleFoldingConsistencyProp 𝔽q β (t := t) (i := Fin.last ℓ)
      (challenges := stmt.challenges) (oStmt := oStmt)
  -- Final constant consistency: the last oracle folded with final
    -- challenges equals constant function
  let lastDomainIdx := getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ)
  have h_eq := getLastOracleDomainIndex_last (ℓ := ℓ) (ϑ := ϑ)
  let k := lastDomainIdx.val
  have h_k: k = ℓ - ϑ := by
    dsimp only [k, lastDomainIdx]
    rw [getLastOraclePositionIndex_last, Nat.sub_mul, Nat.one_mul, Nat.div_mul_cancel (hdiv.out)]
  let curDomainIdx : Fin r := ⟨k, by omega⟩
  have h_destIdx_eq: curDomainIdx.val = lastDomainIdx.val := rfl
  let f_k : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) curDomainIdx :=
    getLastOracle (h_destIdx := h_destIdx_eq) (oracleFrontierIdx := Fin.last ℓ)
      𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (oStmt := oStmt)
  let finalChallenges : Fin ϑ → L := fun cId => stmt.challenges ⟨k + cId, by
    rw [h_k]
    have h_le : ϑ ≤ ℓ := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out)
    have h_cId : cId.val < ϑ := cId.isLt
    have h_last : (Fin.last ℓ).val = ℓ := rfl
    omega
  ⟩
  let destDomainIdx : Fin r := ⟨k + ϑ, by omega⟩
  let strictFinalConstantConsistency: Prop :=
    -- Folding the last oracle gives the constant function
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := curDomainIdx) (steps := ϑ)
      (destIdx := destDomainIdx) (h_destIdx := by rfl)
      (h_destIdx_le := by dsimp only [destDomainIdx]; omega) (f := f_k)
      (r_challenges := finalChallenges) = fun x => stmt.final_constant)

  strictOracleFoldingConsistency ∧ strictFinalConstantConsistency

/-- **Strict round relation for Perfect Completeness**.

This relation uses **exact algebraic equality** instead of proximity measures.
It ensures deterministic preservation with probability 1.

**Important**: This relation is used **only** for Perfect Completeness proofs.
For RBR Knowledge Soundness proofs, use `roundRelation` instead.

Relation at step `i` of the CoreInteraction. `∀ i < ℓ, R_i` must hold at the
beginning of ITERATION `i`. `R_ℓ` must hold after the last iteration and before sending
the final constant. -/
def strictRoundRelation (i : Fin (ℓ + 1)) :
    Set ((Statement (L := L) Context i ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  { input | strictRoundRelationProp (mp := mp) (𝓑 := 𝓑) 𝔽q β i input}

/-- **Strict fold step output relation for Perfect Completeness**.

This is a strict relation (exact equality) used for Perfect Completeness proofs.
For RBR Knowledge Soundness proofs, use `foldStepRelOut` instead.

Input relation for round i: R_i must hold at the beginning of round i -/
def strictFoldStepRelOut (i : Fin ℓ) :
    Set ((Statement (L := L) Context i.succ ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)) ×
      Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ) :=
  { input | strictFoldStepRelOutProp (mp := mp) (𝓑 := 𝓑) 𝔽q β i input}

/-- **Strict final sumcheck relation property** (for Completeness).

This is the strict version of `finalSumcheckRelOutProp` that uses exact equality checks.
Used only for Perfect Completeness proofs.

Note: This requires `t` to be passed in, which should come from the witness in completeness proofs. -/
def strictFinalSumcheckRelOutProp
    (input : ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
      (Unit))) : Prop :=
  -- Final oracle consistency with exact equality
  ∃ (t : MultilinearPoly L ℓ), strictFinalFoldingStateProp 𝔽q β (t := t)
    (h_le := by apply Nat.le_of_dvd (by exact Nat.pos_of_neZero ℓ) (hdiv.out))
    (input := input.1)

/-- **Strict final sumcheck relation for Perfect Completeness**.

This is a strict relation (exact equality) used for Perfect Completeness proofs.
For RBR Knowledge Soundness proofs, use `finalSumcheckRelOut` instead.

Note: In completeness proofs, `t` should come from the witness. -/
def strictFinalSumcheckRelOut :
    Set ((FinalSumcheckStatementOut (L := L) (ℓ := ℓ) ×
      (∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)) ×
      (Unit)) :=
  { input | strictFinalSumcheckRelOutProp 𝔽q β input }

end SumcheckContextIncluded_Relations
end SecurityRelations
end OracleReductionComponents

end Binius.BinaryBasefold
