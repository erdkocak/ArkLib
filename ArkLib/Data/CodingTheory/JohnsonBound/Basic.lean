/- Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, František Silváši
-/
import ArkLib.Data.CodingTheory.JohnsonBound.Lemmas

namespace JohnsonBound

/-!
This module is based on the Johnson Bound section from [listdecoding].
In what follows we reference theorems from [listdecoding] by default.

## References

* [Guruswami, V. and others, *Algorithmic results in list decoding*][listdecoding]
* [Guruswami, V., Rudra, A., and Sudan, M., *Essential coding theory*][codingtheory]
-/

variable {n : ℕ}
         {F : Type} [Fintype F] [DecidableEq F]
         {B : Finset (Fin n → F)} {v : Fin n → F}

/-- The denominator of the bound from Theorem 3.1.
-/
def JohnsonDenominator (B : Finset (Fin n → F)) (v : Fin n → F) : ℚ :=
  let e := e B v
  let d := d B
  let q : ℚ := Fintype.card F
  let frac := q / (q - 1)
  (1- frac * e/n) ^ 2 - (1 - frac * d/n)

lemma johnson_denominator_def :
  JohnsonDenominator B v = ((1 - ((Fintype.card F) / (Fintype.card F - 1)) * (e B v / n)) ^ 2
      - (1 - ((Fintype.card F) / (Fintype.card F - 1)) * (d B/n))) := by
  simp [JohnsonDenominator]
  field_simp

/-- The bound from `Theorem 3.1` makes sense only if the denominator is positive.
This condition ensures that holds.
-/
def JohnsonConditionStrong (B : Finset (Fin n → F)) (v : Fin n → F) : Prop :=
  let e := e B v
  let d := d B
  let q : ℚ := Fintype.card F
  let frac := q / (q - 1)
  (1 - frac * d/n) < (1- frac * e/n) ^ 2

/-- The function used for `q`-ary Johnson Bound.
-/
noncomputable def J (q δ : ℚ) : ℝ :=
  let frac := q / (q - 1)
  (1 / frac) * (1 - Real.sqrt (1 - frac * δ))

/-- A lemma for proving sqrt_le_J
-/
lemma division_by_conjugate {a b : ℝ} (hpos : 0 ≤ b) (hnonzero : a + b.sqrt ≠ 0) :
  a - (b).sqrt = (a^2 - b)/(a + b.sqrt) := by
  rw[eq_div_iff hnonzero]
  ring_nf
  simp_all

lemma sqrt_le_J {q δ : ℚ} (hq : q > 1) (hx0 : 0 ≤ δ) (hx1 : δ ≤ 1) (hqx : q / (q - 1) * δ ≤ 1) :
  1 - ((1-δ) : ℝ).sqrt ≤ J q δ := by
  unfold J
  set frac := q / (q - 1) with hfrac
  have hfrac_ge : frac ≥ 1 := by rw [hfrac, ge_iff_le, one_le_div] <;> grind
  have hx' : 1 - δ ≥ 0 := by linarith
  have hfracx' : 1 - frac * δ ≥ 0 := by nlinarith
  suffices 1 - √(1 - δ) ≤ (1 / frac) * (1 - √(1 - frac * δ)) by simpa
  rw[
    division_by_conjugate (by exact_mod_cast hx') (by positivity),
    division_by_conjugate (by exact_mod_cast hfracx') (by positivity)]
  have : δ = 1 - (1 - δ) := by ring
  have : frac * δ = 1 - (1 - frac * δ) := by ring
  field_simp
  norm_cast
  gcongr
  have : 1 * δ  ≤ frac * δ  := by exact mul_le_mul_of_nonneg_right hfrac_ge hx0
  simp at this
  exact this

/-- The `q`-ary Johnson bound.
-/
def JohnsonConditionWeak (B : Finset (Fin n → F)) (e : ℕ) : Prop :=
  let d := sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }
  let q : ℚ := Fintype.card F
  (e : ℚ) / n < J q (d / n)

lemma johnson_condition_weak_implies_strong [Field F]
  {B : Finset (Fin n → F)}
  {v : Fin n → F}
  {e : ℕ}
  (h_J_cond_weak : JohnsonConditionWeak B e)
  (h_B2_not_one : 1 < (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)).card)
  (h_F_nontriv : 2 ≤ Fintype.card F)
  :
  JohnsonConditionStrong (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)) v := by
  --We show that n > 0, the theorem is ill-posed in this case but it follows from our assumptions.
  have h_n_pos : 0 < n := by
    by_contra hn
    push_neg at hn
    have : n = 0 := by omega
    subst this
    have B_singleton : B.card ≤ 1 := by
      have : ∀ u ∈ B, ∀ v ∈ B, u = v := by
        intros u hu v hv
        funext s
        exact Fin.elim0 s
      have : ¬∃ (u v : B), u ≠ v := by grind
      have neg_of_ineq := (Fintype.one_lt_card_iff.1).mt this
      simp at neg_of_ineq
      exact neg_of_ineq
    have B2_too_small : (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)).card ≤ 1 := by
      have B_supset : B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _) ⊆ B := by grind
      have eval_cards := Finset.card_le_card B_supset
      linarith
    omega
  unfold JohnsonConditionStrong
  intro e_1 d q frac
  -- The real 'proof' is not really by cases, the second case is uninteresting in practice.
  -- However, the theorem still holds when 1 - frac * d / ↑n < 0 and we prove both cases to avoid
  -- adding unnecessary assumptions.
  by_cases h_dsqrt_pos : (0 : ℝ)  ≤ 1 - frac * d / ↑n
  · have h_B2_nonempty : (0 : ℚ) < ((B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)).card : ℚ)
      := by norm_cast; omega
    have h_frac_pos : frac > 0 := by
      unfold frac
      have : 1 < Fintype.card F := by linarith
      field_simp
      unfold q
      exact_mod_cast this
    --The main proof is here, and in the proof of err_n, the rest is algebraic manipulations.
    have j_fun_bound : (↑e / ↑n : ℝ) < (1/↑frac * (1-√(1 - ↑frac * ↑d / ↑n)))  := by
      unfold JohnsonConditionWeak J at h_J_cond_weak
      simp_all
      let d_weak := sInf {d | ∃ u ∈ B, ∃ v ∈ B, ¬u=v ∧ Δ₀(u,v)=d}
      have d_subset : ↑d_weak ≤ (d : ℚ)  := by
          unfold d
          unfold JohnsonBound.d
          unfold d_weak
          have min_dist := min_dist_le_d h_B2_not_one
          have subset_inf_ineq : sInf {d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ Δ₀(u, v) = d} ≤
              sInf {d |
              ∃ u ∈ (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)),
              ∃ v_1 ∈ (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)),
              u ≠ v_1 ∧ Δ₀(u, v_1) = d}:= by
              have subset : {d |
                          ∃ u ∈ (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)),
                          ∃ v_1 ∈ (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)),
                          u ≠ v_1 ∧ Δ₀(u, v_1) = d}
                          ⊆ {d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ Δ₀(u, v) = d} := by
                intro d ⟨u, hu_in, v_1, hv_in, hne, heq⟩
                exact
                  ⟨u, by simp at hu_in; exact hu_in.1, v_1
                  , by simp at hv_in; exact hv_in.1, hne, heq⟩
              gcongr
              obtain ⟨u, hu, v_1, hv_1, hne⟩ := Finset.one_lt_card.mp h_B2_not_one
              use Δ₀(u, v_1)
              exact ⟨u, hu, v_1, hv_1, hne, rfl⟩
          calc ↑d_weak
              = ↑(sInf {d | ∃ u ∈ B, ∃ v ∈ B, ¬u = v ∧ Δ₀(u, v) = d}) := by rfl
            _ ≤ ↑(sInf {d |
              ∃ u ∈ (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)),
              ∃ v_1 ∈ (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)),
              u ≠ v_1 ∧ Δ₀(u, v_1) = d}):= by exact_mod_cast subset_inf_ineq
            _ ≤ JohnsonBound.d (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _)) := by exact_mod_cast min_dist
      have bound: (↑frac)⁻¹ * (1 - √(1 - ↑frac * ↑d_weak / ↑n))
        ≤ (↑frac)⁻¹ * (1 - √(1 - ↑frac * ↑d / ↑n)) := by
        have ineq1 : (↑d_weak / ↑n) ≤ (d / ↑n) := by
          rw[←mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr h_n_pos)]
          field_simp
          exact d_subset
        have ineq2 : frac * (d_weak / n) ≤ frac * (d / n) := by
          exact_mod_cast (mul_le_mul_iff_of_pos_left h_frac_pos).mpr ineq1
        have ineq3 : 1 - frac * (d / n) ≤ 1 - frac * (d_weak / n ) := by linarith
        have ineq3' : (1 : ℝ) - frac * d / n ≤ (1 : ℝ) - frac * d_weak / n := by
          norm_cast; grind
        have ineq4 : √(1 - ↑frac * ↑d / ↑n) ≤ √(1 - ↑frac * ↑d_weak / ↑n) :=
          by exact Real.sqrt_le_sqrt ineq3'
        have ineq5 :  (1 - √(1 - ↑frac * ↑d_weak / ↑n)) ≤ (1 - √(1 - ↑frac * ↑d / ↑n)) := by
          linarith
        simp_all
      have h_J_cond_weak' : ↑e / ↑n < 1 / (↑frac) * (1 - √(1 - frac * (d_weak / ↑n))) := by
        unfold frac
        unfold q
        unfold d_weak
        push_cast
        rw [one_div_div]
        exact h_J_cond_weak
      field_simp
      field_simp at h_J_cond_weak'
      field_simp at bound
      linarith
    have err_n : (↑e_1 / ↑n : ℝ) ≤ (↑e / ↑n : ℝ)   := by
      gcongr
      have err : e_1 ≤ e := by
          unfold e_1
          dsimp[JohnsonBound.e]
          have : ∀ x ∈ B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _), Δ₀(v, x) ≤ e := by
            unfold hammingDist
            simp
            (simp_rw [eq_comm] ; grind)
          have sum_bound :=
            Finset.sum_le_card_nsmul (B ∩ ({x | Δ₀(x, v) ≤ e} : Finset _))
              (fun x => Δ₀(v, x)) e this
          simp
          rw[inv_mul_le_iff₀ h_B2_nonempty]
          exact_mod_cast sum_bound
      exact_mod_cast err
    have j_fun_bound_e1 : (↑e_1 / ↑n : ℝ) < (1/↑frac * (1-√(1 - ↑frac * ↑d / ↑n))) :=
      by linarith [err_n, j_fun_bound]
    have rearrange_jboundw_e1 : √(1 - ↑frac * ↑d / ↑n) < 1 - frac * e_1 / ↑n := by
      have : frac * e_1 / ↑n < 1-√(1 - frac * d / ↑n) := by
        calc ↑frac * ↑e_1 / ↑n
            = ↑frac * (↑e_1 / ↑n) := by ring
          _ < ↑frac * (1/↑frac * (1-√(1 - ↑frac * ↑d / ↑n))) := by
              exact (mul_lt_mul_left (by exact_mod_cast h_frac_pos)).mpr j_fun_bound_e1
          _ = 1-√(1 - ↑frac * ↑d / ↑n) := by ring_nf ; field_simp
      linarith
    have h_esqrtpos :  (0 : ℝ)  ≤ 1- frac * e_1 / ↑n  := by
      have : (0 : ℝ) ≤ √(1 - ↑frac * ↑d / ↑n) := by aesop
      linarith[this, rearrange_jboundw_e1]
    suffices recast_main_goal : (1 - frac * d / ↑n : ℝ) < (1 - frac * e_1 / ↑n) ^ 2 by
     exact_mod_cast recast_main_goal
    suffices roots : √(1 - frac * d / ↑n) < 1- frac * e_1 / ↑n by
      rw[←Real.sqrt_lt h_dsqrt_pos h_esqrtpos]
      exact_mod_cast roots
    exact rearrange_jboundw_e1
  · have strict_neg : 1 - ↑frac * ↑d / ↑n < (0 : ℚ) := by
      have : ¬(0 : ℚ)  ≤ 1 - frac * d / ↑n := by exact_mod_cast h_dsqrt_pos
      rw[Rat.not_le] at this
      exact this
    have nonneg : (0 : ℝ) ≤(1 - ↑frac * ↑e_1 / ↑n) ^ 2  :=
      by exact_mod_cast sq_nonneg (1 - frac * ↑e_1 / ↑n)
    calc 1 - ↑frac * ↑d / ↑n < (0 : ℚ) := strict_neg
      _ ≤ (1 - ↑frac * ↑e_1 / ↑n) ^ 2 := by exact_mod_cast nonneg

private lemma johnson_condition_strong_implies_n_pos
  (h_johnson : JohnsonConditionStrong B v)
  :
  0 < n := by
  cases n <;> try simp [JohnsonConditionStrong] at *

private lemma johnson_condition_strong_implies_2_le_F_card
  (h_johnson : JohnsonConditionStrong B v)
  :
  2 ≤ Fintype.card F := by
  revert h_johnson
  dsimp [JohnsonConditionStrong]
  rcases Fintype.card F with _ | _ | _ <;> aesop

private lemma johnson_condition_strong_implies_2_le_B_card
  (h_johnson : JohnsonConditionStrong B v)
  :
  2 ≤ B.card := by
  dsimp [JohnsonConditionStrong] at h_johnson
  rcases eq : B.card with _ | card | _ <;> [simp_all [e, d]; skip; omega]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 eq
  replace h_johnson : 1 < |1 - (Fintype.card F) / ((Fintype.card F) - 1) * Δ₀(v, a) / (n : ℚ)| := by
    simp_all [e, d, choose_2]
  generalize eq₁ : Fintype.card F = q
  rcases q with _ | _ | q <;> [simp_all; simp_all; skip]
  have h : (Fintype.card F : ℚ) / (Fintype.card F - 1) = 1 + 1 / (Fintype.card F - 1) := by
    have : (Fintype.card F : ℚ) - 1 ≠ 0 := by simp [sub_eq_zero]; omega
    field_simp
  have h' := JohnsonBound.abs_one_sub_div_le_one (v := v) (a := a) (by omega)
  exact absurd (lt_of_lt_of_le (h ▸ h_johnson) h') (lt_irrefl _)

/-- `JohnsonConditionStrong` is equvalent to `JohnsonDenominator` being positive.
-/
lemma johnson_condition_strong_iff_johnson_denom_pos {B : Finset (Fin n → F)} {v : Fin n → F} :
  JohnsonConditionStrong B v ↔ 0 < JohnsonDenominator B v := by
  simp [JohnsonDenominator, JohnsonConditionStrong]

/-- Theorem 3.1.
-/
theorem johnson_bound [Field F]
  (h_condition : JohnsonConditionStrong B v)
  :
  let d := d B
  let q : ℚ := Fintype.card F
  let frac := q / (q - 1)
  B.card ≤ (frac * d/n) / JohnsonDenominator B v
  := by
  suffices B.card * JohnsonDenominator B v ≤
           Fintype.card F / (Fintype.card F - 1) * d B / n by
    rw [johnson_condition_strong_iff_johnson_denom_pos] at h_condition
    rw [←mul_le_mul_right h_condition]
    convert this using 1
    field_simp; rw [mul_div_mul_right]; linarith
  rw [johnson_denominator_def]
  exact JohnsonBound.johnson_bound_lemma
    (johnson_condition_strong_implies_n_pos h_condition)
    (johnson_condition_strong_implies_2_le_B_card h_condition)
    (johnson_condition_strong_implies_2_le_F_card h_condition)

set_option maxHeartbeats 1000000 in
-- Large proof; bump heartbeats.
/-- Alphabet-free Johnson bound from [codingtheory].
-/
theorem johnson_bound_alphabet_free [Field F] [DecidableEq F]
  {B : Finset (Fin n → F)}
  {v : Fin n → F}
  {e : ℕ}
  (hB : 1 < B.card)
  :
  let d := sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }
  let q : ℚ := Fintype.card F
  let frac := q / (q - 1)
  e ≤ n - ((n * (n - d)) : ℝ).sqrt
  →
  (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)).card ≤ q * d * n := by
    -- the proof mostly organized as in the instructions in issue #235,
    -- one major difference is the frac*d/n > 1 subcase which is not covered in the issue.
    intro d q frac h
    let B' := B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)
    -- Helper bounds on parameters.
    have q_not_small : q ≥ (2 : ℚ) := by
      have hF : (2 : ℕ) ≤ Fintype.card F := by
        classical
        have : 1 < Fintype.card F := by
          simpa [Fintype.one_lt_card_iff] using (⟨(0:F), (1:F), by simp⟩ : ∃ a b : F, a ≠ b)
        omega
      simpa [q] using (show (2 : ℚ) ≤ (Fintype.card F : ℚ) from by exact_mod_cast hF)
    have d_not_small : d ≥ 1 := by
      let S : Set ℕ := {d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d}
      have hS_nonempty : S.Nonempty := by
        rcases Finset.one_lt_card.mp hB with ⟨u, hu, v, hv, huv⟩
        refine ⟨hammingDist u v, ?_⟩
        exact ⟨u, hu, v, hv, huv, rfl⟩
      have hLB : ∀ s ∈ S, (1 : ℕ) ≤ s := by
        intro s hs
        rcases hs with ⟨u, hu, v, hv, huv, hdist⟩
        have hpos : 0 < hammingDist u v := hammingDist_pos.mpr huv
        have : 1 ≤ hammingDist u v := (Nat.succ_le_iff).2 hpos
        simpa [S] using (hdist ▸ this)
      simpa [S] using (sInf.le_sInf_of_LB (S := S) hS_nonempty (i := 1) hLB)
    have n_not_small : n ≥ 1 := by
      by_contra hn
      have : n = 0 := by omega
      subst this
      have hcard_le : B.card ≤ 1 := by
        have : ∀ u ∈ B, ∀ v ∈ B, u = v := by
          intro u hu v hv
          funext s
          exact Fin.elim0 s
        exact Finset.card_le_one.2 (by
          intro a ha b hb
          exact this a ha b hb)
      omega

    -- Lower bound on RHS for the small-cardinality case.
    have qdn_not_small : (q * d * n) ≥ 2 := by
      have hdq : (d : ℚ) ≥ (1 : ℚ) := by exact_mod_cast d_not_small
      have hnq : (n : ℚ) ≥ (1 : ℚ) := by exact_mod_cast n_not_small
      have dn_ge_one : (d : ℚ) * (n : ℚ) ≥ (1 : ℚ) := by nlinarith [hdq, hnq]
      have : q * ((d : ℚ) * (n : ℚ)) ≥ (2 : ℚ) := by nlinarith [q_not_small, dn_ge_one]
      simpa [mul_assoc] using this

    by_cases h_size : B'.card < 2
    -- Case: B'.card < 2
    · have hcard_nat : B'.card ≤ 1 := by exact Nat.le_of_lt_succ h_size
      have hcard : (B'.card : ℚ) ≤ (1 : ℚ) := by exact_mod_cast hcard_nat
      have rhs_ge_two : (2 : ℚ) ≤ q * (d : ℚ) * (n : ℚ) := by simpa [mul_assoc] using qdn_not_small
      have rhs_ge_one : (1 : ℚ) ≤ q * (d : ℚ) * (n : ℚ) :=
        le_trans (by norm_num : (1 : ℚ) ≤ 2) rhs_ge_two
      exact le_trans hcard rhs_ge_one

    -- Case: B'.card ≥ 2
    · have hd_le_dB' : (d : ℚ) ≤ JohnsonBound.d B' := by
        have hB'_gt : 1 < B'.card := by omega
        let S : Set ℕ :=
          {d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d}
        let S' : Set ℕ :=
          {d | ∃ u ∈ B', ∃ v ∈ B', u ≠ v ∧ hammingDist u v = d}
        have hsubset : S' ⊆ S := by
          intro t ht
          rcases ht with ⟨u, hu, w, hw, huw, hdist⟩
          have hu' : u ∈ B := by
            have hu'' := hu
            simp [B'] at hu''
            exact hu''.1
          have hw' : w ∈ B := by
            have hw'' := hw
            simp [B'] at hw''
            exact hw''.1
          exact ⟨u, hu', w, hw', huw, hdist⟩
        have hS'nonempty : S'.Nonempty := by
          obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp hB'_gt
          refine ⟨hammingDist u w, ?_⟩
          exact ⟨u, hu, w, hw, huw, rfl⟩
        have h_inf : sInf S ≤ sInf S' := by
          have hmem : sInf S' ∈ S := hsubset (Nat.sInf_mem hS'nonempty)
          exact Nat.sInf_le hmem
        let dmin : ℕ := sInf S'
        have h_inf_nat : d ≤ dmin := by
          simpa [d, S, S', dmin] using h_inf
        have h_inf_q : (d : ℚ) ≤ (dmin : ℚ) := by
          exact_mod_cast h_inf_nat
        have h_min : (dmin : ℚ) ≤ JohnsonBound.d B' := by
          simpa [S', dmin] using (min_dist_le_d (B := B') (by simpa using hB'_gt))
        exact le_trans h_inf_q h_min
      by_cases h_d_close_n : q / (q - 1) * (d / n) > 1
      -- Subcase: frac*d/n > 1
      · have hfrac_dB'_gt_one : q/(q-1) * (JohnsonBound.d B' / n) > 1 := by
          have hn_nonneg : (0 : ℚ) ≤ n := by
            exact_mod_cast (Nat.cast_nonneg n)
          have h_div_le : (d : ℚ) / n ≤ JohnsonBound.d B' / n := by
            exact div_le_div_of_nonneg_right hd_le_dB' hn_nonneg
          have hfrac_nonneg : (0 : ℚ) ≤ q / (q - 1) := by
            have hq_nonneg : (0 : ℚ) ≤ q := by linarith [q_not_small]
            have hq1_nonneg : (0 : ℚ) ≤ q - 1 := by linarith [q_not_small]
            exact div_nonneg hq_nonneg hq1_nonneg
          have h_mul_le :
              q / (q - 1) * (d / n) ≤ q / (q - 1) * (JohnsonBound.d B' / n) := by
            exact mul_le_mul_of_nonneg_left h_div_le hfrac_nonneg
          exact lt_of_lt_of_le h_d_close_n h_mul_le
        have h_strong : JohnsonConditionStrong B' v := by
          have hneg :
              (1 - (q / (q - 1)) * (JohnsonBound.d B' / n) : ℚ) < 0 := by
            linarith [hfrac_dB'_gt_one]
          have hnonneg :
              (0 : ℚ) ≤ (1 - (q / (q - 1)) * (JohnsonBound.e B' v / n)) ^ 2 := by
            exact sq_nonneg (1 - (q / (q - 1)) * (JohnsonBound.e B' v / n))
          have hgoal :
              (1 - (q / (q - 1)) * (JohnsonBound.d B' / n) : ℚ) <
                (1 - (q / (q - 1)) * (JohnsonBound.e B' v / n)) ^ 2 := by
            exact lt_of_lt_of_le hneg hnonneg
          simpa [JohnsonConditionStrong, q, mul_div_assoc] using hgoal

        have johnson_result := johnson_bound h_strong
        have current_bound :
            (B'.card : ℚ) ≤
            (frac * (JohnsonBound.d B') / (n : ℚ)) / JohnsonDenominator B' v := by
          simpa using johnson_result

        have hden_ge :
            JohnsonDenominator B' v ≥
              frac * (JohnsonBound.d B') / (n : ℚ) - 1 := by
          have h' :
              JohnsonDenominator B' v ≥
                ((Fintype.card F : ℚ) / (Fintype.card F - 1))
                  * (JohnsonBound.d B' / n) - 1 := by
            have hsq :
                (0 : ℚ) ≤
                  (1 -
                      ((Fintype.card F : ℚ) / (Fintype.card F - 1))
                        * (JohnsonBound.e B' v / n)) ^ 2 := by
              exact sq_nonneg _
            calc
              JohnsonDenominator B' v =
                  (1 -
                      ((Fintype.card F : ℚ) / (Fintype.card F - 1))
                        * (JohnsonBound.e B' v / n)) ^ 2
                    -
                      (1 -
                        ((Fintype.card F : ℚ) / (Fintype.card F - 1))
                          * (JohnsonBound.d B' / n)) := by
                simp [JohnsonDenominator, mul_div_assoc]
              _ = (1 -
                      ((Fintype.card F : ℚ) / (Fintype.card F - 1))
                        * (JohnsonBound.e B' v / n)) ^ 2
                    - 1
                    + ((Fintype.card F : ℚ) / (Fintype.card F - 1))
                        * (JohnsonBound.d B' / n) := by
                ring
              _ ≥ (-1)
                    + ((Fintype.card F : ℚ) / (Fintype.card F - 1))
                        * (JohnsonBound.d B' / n) := by
                linarith [hsq]
              _ = ((Fintype.card F : ℚ) / (Fintype.card F - 1))
                    * (JohnsonBound.d B' / n) - 1 := by
                ring
          simpa [q, frac, mul_div_assoc] using h'
        have hgap : frac * (JohnsonBound.d B') / (n:ℚ) - 1 ≥ 1 / ((n:ℚ) * (q-1)) := by
          have hq1_pos : (0 : ℚ) < q - 1 := by
            linarith [q_not_small]
          have hn_pos : (0 : ℚ) < n := by
            have hn' : (1 : ℚ) ≤ n := by exact_mod_cast n_not_small
            linarith
          have hq1_ne : (q - 1 : ℚ) ≠ 0 := by exact ne_of_gt hq1_pos
          have hn_ne : (n : ℚ) ≠ 0 := by exact ne_of_gt hn_pos
          have hqd_gt : (q - 1) * (n : ℚ) < q * (d : ℚ) := by
            have h' := h_d_close_n
            field_simp [hq1_ne, hn_ne] at h'
            have hden_pos : (0 : ℚ) < (q - 1) * n := by
              exact mul_pos hq1_pos hn_pos
            have h'' :
                (1 : ℚ) * ((q - 1) * n) < q * (d : ℚ) :=
              (_root_.lt_div_iff₀ hden_pos).1 h'
            simpa [mul_comm, mul_left_comm, mul_assoc] using h''
          have hF2 : (2 : ℕ) ≤ Fintype.card F := by
            exact_mod_cast (by simpa [q] using q_not_small)
          have hF1 : (1 : ℕ) ≤ Fintype.card F := by omega
          have hqd_gt' :
              ((Fintype.card F : ℚ) * (d : ℚ) >
                ((Fintype.card F - 1 : ℕ) : ℚ) * (n : ℚ)) := by
            have hqd_gt'' :
                ((Fintype.card F : ℚ) * (d : ℚ) >
                  ((Fintype.card F : ℚ) - 1) * (n : ℚ)) := by
              simpa [q] using hqd_gt
            simpa [Nat.cast_sub hF1] using hqd_gt''
          have hqd_gt_nat :
              (Fintype.card F) * d > (Fintype.card F - 1) * n := by
            exact_mod_cast hqd_gt'
          have hqd_ge_nat :
              (Fintype.card F - 1) * n ≤ (Fintype.card F) * d :=
            Nat.le_of_lt hqd_gt_nat
          have hnum_ge_nat :
              1 ≤ (Fintype.card F) * d - (Fintype.card F - 1) * n := by
            exact (Nat.succ_le_iff).2 (Nat.sub_pos_of_lt hqd_gt_nat)
          have hnum_ge_q :
              (1 : ℚ) ≤ q * (d : ℚ) - (q - 1) * (n : ℚ) := by
            have hnum_ge_q' :
                (1 : ℚ) ≤
                  ((Fintype.card F) * d - (Fintype.card F - 1) * n : ℚ) := by
              exact_mod_cast hnum_ge_nat
            simpa [q, Nat.cast_sub hF1, Nat.cast_sub hqd_ge_nat, Nat.cast_mul] using hnum_ge_q'
          have hgap_d : (1 : ℚ) / ((n : ℚ) * (q - 1)) ≤ frac * (d : ℚ) / n - 1 := by
            have hden_nonneg : (0 : ℚ) ≤ (q - 1) * n := by
              exact mul_nonneg (le_of_lt hq1_pos) (le_of_lt hn_pos)
            calc
              (1 : ℚ) / ((n : ℚ) * (q - 1))
                  = (1 : ℚ) / ((q - 1) * n) := by
                      simp [mul_comm]
              _ ≤ (q * (d : ℚ) - (q - 1) * (n : ℚ)) / ((q - 1) * n) := by
                      exact div_le_div_of_nonneg_right hnum_ge_q hden_nonneg
              _ = frac * (d : ℚ) / n - 1 := by
                      field_simp [frac, hq1_ne, hn_ne]
          have hn_nonneg : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
          have hfrac_nonneg : (0 : ℚ) ≤ frac := by
            have hq_nonneg : (0 : ℚ) ≤ q := by linarith [q_not_small]
            have hq1_nonneg : (0 : ℚ) ≤ q - 1 := by linarith [q_not_small]
            exact div_nonneg hq_nonneg hq1_nonneg
          have h_div_le : (d : ℚ) / n ≤ JohnsonBound.d B' / n := by
            exact div_le_div_of_nonneg_right hd_le_dB' hn_nonneg
          have h_mul_le' :
              frac * (d / n) ≤ frac * (JohnsonBound.d B' / n) := by
            exact mul_le_mul_of_nonneg_left h_div_le hfrac_nonneg
          have h_mul_le :
              frac * (d : ℚ) / n ≤ frac * (JohnsonBound.d B') / n := by
            simpa [mul_div_assoc] using h_mul_le'
          have h_mul_le' :
              frac * (d : ℚ) / n - 1 ≤ frac * (JohnsonBound.d B') / n - 1 := by
            linarith [h_mul_le]
          exact le_trans hgap_d h_mul_le'
        have hfrac_bound :
            (frac * (JohnsonBound.d B') / (n:ℚ)) / JohnsonDenominator B' v ≤
            q * JohnsonBound.d B' := by
          have hden_lb : (1 : ℚ) / ((n : ℚ) * (q - 1)) ≤ JohnsonDenominator B' v := by
            linarith [hden_ge, hgap]
          have hn_pos_nat : 0 < n := (Nat.succ_le_iff).1 n_not_small
          have hn_pos : (0 : ℚ) < n := by exact_mod_cast hn_pos_nat
          have hq1_pos : (0 : ℚ) < q - 1 := by linarith [q_not_small]
          have hden_pos : (0 : ℚ) < (1 : ℚ) / ((n : ℚ) * (q - 1)) := by
            have hmul_pos : (0 : ℚ) < (n : ℚ) * (q - 1) := by
              exact mul_pos hn_pos hq1_pos
            exact one_div_pos.mpr hmul_pos
          have hnum_nonneg : (0 : ℚ) ≤ frac * (JohnsonBound.d B') / (n : ℚ) := by
            have hd0 : (0 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (Nat.zero_le d)
            have hd_nonneg : (0 : ℚ) ≤ JohnsonBound.d B' := by
              exact le_trans hd0 hd_le_dB'
            have hfrac_nonneg : (0 : ℚ) ≤ frac := by
              have hq_nonneg : (0 : ℚ) ≤ q := by linarith [q_not_small]
              have hq1_nonneg : (0 : ℚ) ≤ q - 1 := by linarith [q_not_small]
              exact div_nonneg hq_nonneg hq1_nonneg
            have hn_nonneg : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
            have hmul_nonneg : (0 : ℚ) ≤ frac * JohnsonBound.d B' := by
              exact mul_nonneg hfrac_nonneg hd_nonneg
            exact div_nonneg hmul_nonneg hn_nonneg
          have hstep :
              (frac * (JohnsonBound.d B') / (n : ℚ)) / JohnsonDenominator B' v ≤
              (frac * (JohnsonBound.d B') / (n : ℚ)) /
                (1 / ((n : ℚ) * (q - 1))) := by
            exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_lb
          calc
            (frac * (JohnsonBound.d B') / (n : ℚ)) / JohnsonDenominator B' v
                ≤ (frac * (JohnsonBound.d B') / (n : ℚ)) /
                    (1 / ((n : ℚ) * (q - 1))) := hstep
            _ = q * JohnsonBound.d B' := by
                  have hn_ne : (n : ℚ) ≠ 0 := by exact ne_of_gt hn_pos
                  have hq1_ne : (q - 1 : ℚ) ≠ 0 := by exact ne_of_gt hq1_pos
                  field_simp [frac, hn_ne, hq1_ne]
                  simp [mul_comm]
        have le_q_times_d : (B'.card : ℚ) ≤ q * JohnsonBound.d B' := by
          linarith [current_bound, hfrac_bound]
        have le_q_times_n : (B'.card : ℚ) ≤ q * (n : ℚ) := by
          have hB'_ge2 : 2 ≤ B'.card := by
            exact le_of_not_gt h_size
          have hq_nonneg : (0 : ℚ) ≤ q := by linarith [q_not_small]
          have hd_le_n : JohnsonBound.d B' ≤ (n : ℚ) := by
            classical
            have hB2_card :
                2 * choose_2 (B'.card : ℚ) =
                  {x ∈ B' ×ˢ B' | x.1 ≠ x.2}.card := by
              simp
              unfold choose_2
              ring_nf
              have BBcard : (B' ×ˢ B').card = B'.card ^ 2 := by
                rw [Finset.card_product, sq]
              have BBdiagcard : {x ∈ B' ×ˢ B' | x.1 = x.2}.card = B'.card := by
                simp
              have BBdisjoint :
                  {x ∈ B' ×ˢ B' | x.1 = x.2} ∩ {x ∈ B' ×ˢ B' | x.1 ≠ x.2} = ∅ := by
                ext x
                simp
                tauto
              have BBunion :
                  B' ×ˢ B' =
                    {x ∈ B' ×ˢ B' | x.1 = x.2} ∪ {x ∈ B' ×ˢ B' | x.1 ≠ x.2} := by
                ext ⟨a, b⟩
                simp
                tauto
              have BBcount :
                  {x ∈ B' ×ˢ B' | x.1 ≠ x.2}.card
                    = (B' ×ˢ B').card - {x ∈ B' ×ˢ B' | x.1 = x.2}.card := by
                rw [BBunion, Finset.card_union, BBdiagcard, BBdisjoint]
                have doubleindex1 :
                    {x ∈ {x ∈ B' ×ˢ B' | x.1 = x.2} ∪
                        {x ∈ B' ×ˢ B' | x.1 ≠ x.2} | x.1 = x.2}
                      = {x ∈ B' ×ˢ B' | x.1 = x.2} := by
                  ext x
                  simp
                  tauto
                have doubleindex2 :
                    {x ∈ {x ∈ B' ×ˢ B' | x.1 = x.2} ∪
                        {x ∈ B' ×ˢ B' | x.1 ≠ x.2} | x.1 ≠ x.2}
                      = {x ∈ B' ×ˢ B' | x.1 ≠ x.2} := by
                  ext x
                  simp
                  tauto
                rw [doubleindex1, BBdiagcard]
                simp
                rw [doubleindex2]
              rw [BBcount, BBcard, BBdiagcard]
              rw [Nat.cast_sub]
              ring_nf
              rfl
              nlinarith [sq_nonneg (B'.card - 1)]
            have hdist_le :
                ∀ x ∈ {x ∈ B' ×ˢ B' | x.1 ≠ x.2},
                  (Δ₀(x.1, x.2) : ℚ) ≤ n := by
              intro x hx
              have : Δ₀(x.1, x.2) ≤ n := by
                simpa using (hammingDist_le_card_fintype (x := x.1) (y := x.2))
              exact_mod_cast this
            have hsum_le :
                ∑ x ∈ {x ∈ B' ×ˢ B' | x.1 ≠ x.2}, (Δ₀(x.1, x.2) : ℚ)
                  ≤ (n : ℚ) * ({x ∈ B' ×ˢ B' | x.1 ≠ x.2}.card) := by
              calc
                ∑ x ∈ {x ∈ B' ×ˢ B' | x.1 ≠ x.2}, (Δ₀(x.1, x.2) : ℚ)
                    ≤ ∑ x ∈ {x ∈ B' ×ˢ B' | x.1 ≠ x.2}, (n : ℚ) := by
                      exact Finset.sum_le_sum hdist_le
                _ = (n : ℚ) * ({x ∈ B' ×ˢ B' | x.1 ≠ x.2}.card) := by
                      simp [Finset.sum_const, mul_comm]
            have hsum_le' :
                ∑ x ∈ {x ∈ B' ×ˢ B' | x.1 ≠ x.2}, (Δ₀(x.1, x.2) : ℚ)
                  ≤ (n : ℚ) * (2 * choose_2 (B'.card : ℚ)) := by
              simpa [hB2_card, mul_comm, mul_left_comm, mul_assoc] using hsum_le
            have hB'_gt : 1 < B'.card := by
              omega
            have hS_nonempty :
                {x ∈ B' ×ˢ B' | x.1 ≠ x.2}.Nonempty := by
              obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hB'_gt
              refine ⟨⟨u, v⟩, ?_⟩
              simp [hu, hv, huv]
            have hden_pos : (0 : ℚ) < 2 * choose_2 (B'.card : ℚ) := by
              have hS_pos : (0 : ℚ) < {x ∈ B' ×ˢ B' | x.1 ≠ x.2}.card := by
                exact_mod_cast (Finset.card_pos.mpr hS_nonempty)
              simpa [hB2_card] using hS_pos
            have hdiv_le :
                (∑ x ∈ {x ∈ B' ×ˢ B' | x.1 ≠ x.2}, (Δ₀(x.1, x.2) : ℚ)) /
                  (2 * choose_2 (B'.card : ℚ)) ≤ (n : ℚ) := by
              exact (_root_.div_le_iff₀ hden_pos).2 (by
                simpa [mul_comm, mul_left_comm, mul_assoc] using hsum_le')
            simpa [JohnsonBound.d, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
              hdiv_le
          exact le_trans le_q_times_d (mul_le_mul_of_nonneg_left hd_le_n hq_nonneg)
        have final : (B'.card : ℚ) ≤ q * d * (n : ℚ) := by
          have hn_nonneg : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
          have hq_nonneg : (0 : ℚ) ≤ q := by linarith [q_not_small]
          have hqn_nonneg : (0 : ℚ) ≤ q * (n : ℚ) := by
            exact mul_nonneg hq_nonneg hn_nonneg
          have hd_ge1 : (1 : ℚ) ≤ (d : ℚ) := by
            exact_mod_cast d_not_small
          have hstep : q * (n : ℚ) ≤ q * (d : ℚ) * (n : ℚ) := by
            have hmul :
                q * (n : ℚ) * (1 : ℚ) ≤ q * (n : ℚ) * (d : ℚ) := by
              exact mul_le_mul_of_nonneg_left hd_ge1 hqn_nonneg
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
          exact le_trans le_q_times_n hstep
        exact_mod_cast final

      -- Subcase: frac*d/n ≤ 1 (main case)
      · have d_le_n : d ≤ n := by
          let S : Set ℕ :=
            {d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d}
          obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hB
          have hdist_le : hammingDist u v ≤ n := by
            simpa using (hammingDist_le_card_fintype (x := u) (y := v))
          have hdist_in : hammingDist u v ∈ S := by
            exact ⟨u, hu, v, hv, huv, rfl⟩
          have hdist_ge : d ≤ hammingDist u v := by
            simpa [d, S] using (Nat.sInf_le hdist_in)
          exact le_trans hdist_ge hdist_le
        -- Helper positivity facts for the main-case algebra.
        have hn_pos_nat : 0 < n := (Nat.succ_le_iff).1 n_not_small
        have hn_pos : (0 : ℚ) < n := by exact_mod_cast hn_pos_nat
        have hn_nonneg : (0 : ℚ) ≤ n := by exact_mod_cast (Nat.cast_nonneg n)
        have hq_pos : (0 : ℚ) < q := by linarith [q_not_small]
        have hq1_pos : (0 : ℚ) < q - 1 := by linarith [q_not_small]
        have hq_ne : (q : ℚ) ≠ 0 := by exact ne_of_gt hq_pos
        have hq1_ne : (q - 1 : ℚ) ≠ 0 := by exact ne_of_gt hq1_pos
        have hfrac_pos : (0 : ℚ) < frac := by
          exact div_pos hq_pos hq1_pos
        have hfrac_gt1 : (1 : ℚ) < frac := by
          have hq1_lt : (q - 1 : ℚ) < q := by linarith
          have h := (one_lt_div hq1_pos).2 hq1_lt
          simpa [frac] using h
        have hfrac_ne : (frac : ℚ) ≠ 0 := by
          simpa [frac] using (div_ne_zero hq_ne hq1_ne)
        have hn2_nonneg : (0 : ℚ) ≤ (n : ℚ) ^ 2 := by
          exact sq_nonneg (n : ℚ)
        have hn2_pos : (0 : ℚ) < (n : ℚ) ^ 2 := by
          exact pow_pos hn_pos _
        have h_johnson_strong : JohnsonConditionStrong B' v := by
          have h_johnson_weak : JohnsonConditionWeak B e := by
            have h_muln : (e : ℚ) / n ≤ 1 - ((1 - (d : ℚ) / n) : ℝ).sqrt := by
              by_cases hn : n = 0
              · subst hn
                simp
              · have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by
                  exact_mod_cast (Nat.cast_nonneg n)
                have hn' : (n : ℝ) ≠ 0 := by
                  exact_mod_cast hn
                have h_div : (e : ℝ) / n ≤ (n - ((n * (n - d) : ℝ).sqrt)) / n := by
                  exact (div_le_div_of_nonneg_right (by simpa using h) hn_nonneg)
                have h_div' : (e : ℝ) / n ≤ 1 - ((n * (n - d) : ℝ).sqrt) / n := by
                  simpa [sub_div, hn'] using h_div
                have h_sqrt :
                    ((n * (n - d) : ℝ).sqrt) / n =
                    ((1 - (d : ℝ) / n) : ℝ).sqrt := by
                  have hsq_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by
                    exact sq_nonneg (n : ℝ)
                  calc
                    ((n * (n - d) : ℝ).sqrt) / n
                        = ((n * (n - d) : ℝ).sqrt) / ((n : ℝ) ^ 2).sqrt := by
                            have h_sqrt_n : ((n : ℝ) ^ 2).sqrt = (n : ℝ) := by
                              simp [hn_nonneg]
                            simp [h_sqrt_n]
                    _ = (((n * (n - d) : ℝ) / (n : ℝ) ^ 2).sqrt) := by
                            symm
                            exact Real.sqrt_div' ((n : ℝ) * (n - d)) hsq_nonneg
                    _ = (((n - d) / n : ℝ).sqrt) := by
                            have hfrac : ((n : ℝ) * (n - d)) / (n : ℝ) ^ 2 = (n - d) / n := by
                              field_simp [hn']
                              ring
                            simp [hfrac]
                    _ = ((1 - (d : ℝ) / n) : ℝ).sqrt := by
                            calc
                              ((n - d) / n : ℝ).sqrt
                                  = (((n : ℝ) - (d : ℝ)) / n).sqrt := by
                                    simp
                              _ = ((1 - (d : ℝ) / n) : ℝ).sqrt := by
                                    simp [sub_div, hn']
                have h_final :
                    (e : ℝ) / n ≤ 1 - ((1 - (d : ℝ) / n) : ℝ).sqrt := by
                  calc
                    (e : ℝ) / n ≤ 1 - ((n * (n - d) : ℝ).sqrt) / n := h_div'
                    _ = 1 - ((1 - (d : ℝ) / n) : ℝ).sqrt := by
                        rw [h_sqrt]
                simpa using h_final
            have h_J_bound : 1 - ((1 - (d : ℚ) / n) : ℝ).sqrt ≤ J q (d / n) := by
              have hq : q > 1 := by
                classical
                have hF : (2 : ℕ) ≤ Fintype.card F := by
                  have : 1 < Fintype.card F := by
                    simpa [Fintype.one_lt_card_iff] using
                      (⟨(0 : F), (1 : F), by simp⟩ : ∃ a b : F, a ≠ b)
                  omega
                have hq2 : (2 : ℚ) ≤ q := by
                  simpa [q] using
                    (show (2 : ℚ) ≤ (Fintype.card F : ℚ) from by exact_mod_cast hF)
                linarith
              have hx0 : (0 : ℚ) ≤ d / n := by
                exact div_nonneg (by exact_mod_cast (Nat.cast_nonneg d))
                  (by exact_mod_cast (Nat.cast_nonneg n))
              have hx1 : d / n ≤ (1 : ℚ) := by
                by_cases hn : n = 0
                · simp [hn]
                · have hnpos : (0 : ℚ) < n := by
                    exact_mod_cast (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
                  have hd : (d : ℚ) ≤ n := by exact_mod_cast d_le_n
                  exact (div_le_one hnpos).2 hd
              have hqx : q / (q - 1) * (d / n) ≤ (1 : ℚ) := by
                exact le_of_not_gt h_d_close_n
              simpa using (sqrt_le_J (q := q) (δ := d / n) hq hx0 hx1 hqx)
            have h_le : (e : ℚ) / n ≤  J q (d / n) := by
              linarith [h_muln ,h_J_bound]
            have h_ne : ((e : ℚ) / n : ℝ)  ≠  J q (d / n) := by
              intro h_eq
              have h_eq' : (1 - ((1 - (d : ℚ) / n) : ℝ).sqrt) = J q (d / n) := by
                apply le_antisymm
                · exact h_J_bound
                · calc
                    J q (d / n) = ((e : ℚ) / n : ℝ) := by symm; exact h_eq
                    _ ≤ 1 - ((1 - (d : ℚ) / n) : ℝ).sqrt := h_muln
              set δ : ℚ := d / n
              set frac : ℚ := q / (q - 1)
              have h_eqJ :
                  (1 - ((1 - δ) : ℝ).sqrt) =
                    (1 / frac) * (1 - Real.sqrt (1 - frac * δ)) := by
                simpa [J, δ, frac] using h_eq'
              have d_not_small : d ≥ 1 := by
                let S : Set ℕ :=
                  {d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d}
                have hS_nonempty : S.Nonempty := by
                  rcases Finset.one_lt_card.mp hB with ⟨u, hu, v, hv, huv⟩
                  refine ⟨hammingDist u v, ?_⟩
                  exact ⟨u, hu, v, hv, huv, rfl⟩
                have hLB : ∀ s ∈ S, (1 : ℕ) ≤ s := by
                  intro s hs
                  rcases hs with ⟨u, hu, v, hv, huv, hdist⟩
                  have hpos : 0 < hammingDist u v := hammingDist_pos.mpr huv
                  have : 1 ≤ hammingDist u v := (Nat.succ_le_iff).2 hpos
                  simpa [S] using (hdist ▸ this)
                simpa [S] using (sInf.le_sInf_of_LB (S := S) hS_nonempty (i := 1) hLB)
              have hn_pos : 0 < n := by
                by_contra hn
                have : n = 0 := by omega
                subst this
                have hcard_le : B.card ≤ 1 := by
                  have : ∀ u ∈ B, ∀ v ∈ B, u = v := by
                    intro u hu v hv
                    funext s
                    exact Fin.elim0 s
                  exact Finset.card_le_one.2 (by
                    intro a ha b hb
                    exact this a ha b hb)
                omega
              have hδ_pos : (0 : ℚ) < δ := by
                have hd_pos : 0 < d := (Nat.succ_le_iff).1 d_not_small
                have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd_pos
                have hnq : (0 : ℚ) < n := by exact_mod_cast hn_pos
                simpa [δ] using (div_pos hdq hnq)
              have hδ_ne : (δ : ℝ) ≠ 0 := by
                exact ne_of_gt (by exact_mod_cast hδ_pos)
              have hδ_nonneg : (0 : ℚ) ≤ δ := by
                exact le_of_lt hδ_pos
              have hq : q > 1 := by
                classical
                have hF : (2 : ℕ) ≤ Fintype.card F := by
                  have : 1 < Fintype.card F := by
                    simpa [Fintype.one_lt_card_iff] using
                      (⟨(0 : F), (1 : F), by simp⟩ : ∃ a b : F, a ≠ b)
                  omega
                have hq2 : (2 : ℚ) ≤ q := by
                  simpa [q] using
                    (show (2 : ℚ) ≤ (Fintype.card F : ℚ) from by exact_mod_cast hF)
                linarith
              have hfrac_gt : (1 : ℚ) < frac := by
                have hq1 : (0 : ℚ) < q - 1 := by linarith [hq]
                have hq' : (q - 1) < q := by linarith
                simpa [frac] using (one_lt_div hq1).2 hq'
              have hfrac_ge : (1 : ℚ) ≤ frac := by exact le_of_lt hfrac_gt
              have hfrac_ne1 : (frac : ℝ) ≠ 1 := by
                exact ne_of_gt (by exact_mod_cast hfrac_gt)
              have hfrac_ne0 : (frac : ℝ) ≠ 0 := by
                have hfrac_pos : (0 : ℚ) < frac := by linarith [hfrac_gt]
                exact ne_of_gt (by exact_mod_cast hfrac_pos)
              have hqx : frac * δ ≤ 1 := by
                have hqx' : q / (q - 1) * (d / n) ≤ 1 := by
                  exact le_of_not_gt h_d_close_n
                simpa [frac, δ] using hqx'
              have hδ_le_fracδ : δ ≤ frac * δ := by
                have := mul_le_mul_of_nonneg_right hfrac_ge hδ_nonneg
                simpa [one_mul] using this
              have hδ_le_one : δ ≤ 1 := by exact le_trans hδ_le_fracδ hqx
              have hpos_left : (0 : ℝ) ≤ 1 - (δ : ℝ) := by
                exact_mod_cast (by linarith [hδ_le_one])
              have hpos_right : (0 : ℝ) ≤ 1 - (frac : ℚ) * δ := by
                exact_mod_cast (by linarith [hqx])
              have hden_left : (1 : ℝ) + Real.sqrt (1 - (δ : ℝ)) ≠ 0 := by
                have : (0 : ℝ) ≤ Real.sqrt (1 - (δ : ℝ)) := by
                  exact Real.sqrt_nonneg _
                linarith
              have hden_right :
                  (1 : ℝ) + Real.sqrt (1 - (frac : ℝ) * (δ : ℝ)) ≠ 0 := by
                have : (0 : ℝ) ≤ Real.sqrt (1 - (frac : ℝ) * (δ : ℝ)) := by
                  exact Real.sqrt_nonneg _
                linarith
              have h_left :
                  1 - Real.sqrt (1 - (δ : ℝ)) =
                    (δ : ℝ) / (1 + Real.sqrt (1 - (δ : ℝ))) := by
                have h :=
                  division_by_conjugate (a := (1 : ℝ)) (b := 1 - (δ : ℝ)) hpos_left hden_left
                calc
                  1 - Real.sqrt (1 - (δ : ℝ))
                      = ((1 : ℝ)^2 - (1 - (δ : ℝ))) /
                          (1 + Real.sqrt (1 - (δ : ℝ))) := by
                        simpa using h
                  _ = (δ : ℝ) / (1 + Real.sqrt (1 - (δ : ℝ))) := by
                        ring
              have h_right :
                  1 - Real.sqrt (1 - (frac : ℝ) * (δ : ℝ)) =
                    ((frac : ℝ) * (δ : ℝ)) /
                      (1 + Real.sqrt (1 - (frac : ℝ) * (δ : ℝ))) := by
                have h :=
                  division_by_conjugate (a := (1 : ℝ)) (b := 1 - (frac : ℝ) * (δ : ℝ))
                    hpos_right hden_right
                calc
                  1 - Real.sqrt (1 - (frac : ℝ) * (δ : ℝ))
                      = ((1 : ℝ)^2 - (1 - (frac : ℝ) * (δ : ℝ))) /
                          (1 + Real.sqrt (1 - (frac : ℝ) * (δ : ℝ))) := by
                        simpa using h
                  _ = ((frac : ℝ) * (δ : ℝ)) /
                        (1 + Real.sqrt (1 - (frac : ℝ) * (δ : ℝ))) := by
                        ring
              have h_eq_div := h_eqJ
              simp [h_left, h_right] at h_eq_div
              have h_eq_div' :
                  (δ : ℝ) / (1 + Real.sqrt (1 - (δ : ℝ))) =
                    (δ : ℝ) / (1 + Real.sqrt (1 - (frac : ℝ) * (δ : ℝ))) := by
                simpa [mul_div_assoc, hfrac_ne0, mul_comm, mul_left_comm, mul_assoc] using h_eq_div
              have h_eq_mul :
                  (δ : ℝ) * (1 + Real.sqrt (1 - (frac : ℝ) * (δ : ℝ))) =
                    (δ : ℝ) * (1 + Real.sqrt (1 - (δ : ℝ))) := by
                exact (div_eq_div_iff hden_left hden_right).1 h_eq_div'
              have h_eq_den :
                  1 + Real.sqrt (1 - (frac : ℝ) * (δ : ℝ)) =
                    1 + Real.sqrt (1 - (δ : ℝ)) := by
                exact mul_left_cancel₀ hδ_ne h_eq_mul
              have h_sqrt_eq :
                  Real.sqrt (1 - (frac : ℝ) * (δ : ℝ)) =
                    Real.sqrt (1 - (δ : ℝ)) := by
                exact add_left_cancel h_eq_den
              have h_sq := congrArg (fun x => x^2) h_sqrt_eq
              simp [Real.sq_sqrt hpos_right, Real.sq_sqrt hpos_left] at h_sq
              have h_mul_eq : (frac : ℝ) * (δ : ℝ) = (δ : ℝ) := by
                linarith [h_sq]
              have h_mul_eq' : (frac : ℝ) * (δ : ℝ) = (1 : ℝ) * (δ : ℝ) := by
                simpa using h_mul_eq
              have hfrac_eq : (frac : ℝ) = 1 := by
                exact mul_right_cancel₀ hδ_ne h_mul_eq'
              exact hfrac_ne1 hfrac_eq
            exact lt_of_le_of_ne h_le h_ne
          have h_size' : 1 < B'.card := by
            omega
          have hF_nontriv : (2 : ℕ) ≤ Fintype.card F := by
            have : 1 < Fintype.card F := by
              simpa [Fintype.one_lt_card_iff] using (⟨(0:F), (1:F), by simp⟩ : ∃ a b : F, a ≠ b)
            omega
          exact johnson_condition_weak_implies_strong h_johnson_weak h_size' hF_nontriv

        have johnson_result := johnson_bound h_johnson_strong

        have current_bound :
            (B'.card : ℚ) ≤
            (frac * (JohnsonBound.d B') / (n : ℚ)) / JohnsonDenominator B' v := by
          simpa using johnson_result

        -- Core inequality from the hypothesis (reused below).
        have h_div' :
            1 - (d : ℝ) / n ≤ (1 - (e : ℝ) / n) ^ 2 := by
          have h_sqrt_le :
              Real.sqrt ((n * (n - d)) : ℝ) ≤ (n : ℝ) - e := by
            linarith [h]
          have h_sqrt_nonneg :
              (0 : ℝ) ≤ Real.sqrt ((n * (n - d)) : ℝ) := by
            exact Real.sqrt_nonneg _
          have h_nd_nonneg : (0 : ℝ) ≤ (n : ℝ) - d := by
            exact sub_nonneg.mpr (by exact_mod_cast d_le_n)
          have h_nnd_nonneg : (0 : ℝ) ≤ (n : ℝ) * (n - d) := by
            exact mul_nonneg (by exact_mod_cast (Nat.cast_nonneg n)) h_nd_nonneg
          have h_sq_le :
              (n * (n - d) : ℝ) ≤ ((n : ℝ) - e) ^ 2 := by
            have h_sq := mul_self_le_mul_self h_sqrt_nonneg h_sqrt_le
            have h_sq' :
                (Real.sqrt (n * (n - d) : ℝ)) ^ 2 ≤ ((n : ℝ) - e) ^ 2 := by
              rw [pow_two, pow_two]
              exact h_sq
            have h_sq'' := h_sq'
            rw [Real.sq_sqrt h_nnd_nonneg] at h_sq''
            exact h_sq''
          have hn_pos_real : (0 : ℝ) < n := by
            exact_mod_cast (Nat.succ_le_iff).1 n_not_small
          have hn_ne_real : (n : ℝ) ≠ 0 := by exact ne_of_gt hn_pos_real
          have h_div :
              (n * (n - d) : ℝ) / n ^ 2 ≤ ((n : ℝ) - e) ^ 2 / n ^ 2 := by
            exact (div_le_div_of_nonneg_right h_sq_le (by nlinarith [hn_pos_real]))
          have h_left :
              (n * (n - d) : ℝ) / n ^ 2 = 1 - (d : ℝ) / n := by
            field_simp [hn_ne_real]
            ring
          have h_right :
              ((n : ℝ) - e) ^ 2 / n ^ 2 = (1 - (e : ℝ) / n) ^ 2 := by
            field_simp [hn_ne_real]
          simpa [h_left, h_right] using h_div
        have h_div'_q : (1 - (d / n : ℚ)) ≤ (1 - (e / n : ℚ)) ^ 2 := by
          have h_div'_real :
              ((1 - (d / n : ℚ)) : ℝ) ≤ ((1 - (e / n : ℚ)) ^ 2 : ℝ) := by
            simpa using h_div'
          exact_mod_cast h_div'_real

        have last_bound :
            (frac * (JohnsonBound.d B') / (n : ℚ)) / JohnsonDenominator B' v ≤
            q * (d : ℚ) * (n : ℚ) := by
          set D0 : ℚ := d / n
          set E0 : ℚ := e / n
          set Den : ℚ := D0 - 2 * E0 + frac * E0 ^ 2
          have quad_nonneg : (0 : ℚ) ≤ D0 - 2 * E0 + E0 ^ 2 := by
            have htmp_q :
                (0 : ℚ) ≤ (1 - (e / n : ℚ)) ^ 2 - (1 - (d / n : ℚ)) := by
              linarith [h_div'_q]
            have h_eq_q :
                (1 - (e / n : ℚ)) ^ 2 - (1 - (d / n : ℚ)) =
                  D0 - 2 * E0 + E0 ^ 2 := by
              ring
            simpa [h_eq_q] using htmp_q
          have frac_sub_one_eq : frac - 1 = (1 : ℚ) / (q - 1) := by
            field_simp [frac, hq1_ne]
          have one_div_q_le : (1 : ℚ) / q ≤ frac - 1 := by
            have hq1_le_q : (q - 1 : ℚ) ≤ q := by linarith
            have h1 : (1 : ℚ) / q ≤ (1 : ℚ) / (q - 1) := by
              exact (one_div_le_one_div_of_le hq1_pos hq1_le_q)
            simpa [frac_sub_one_eq] using h1
          -- 1. Expand JohnsonDenominator.
          have denom_expansion : JohnsonDenominator B' v =
              frac * (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
              frac * (JohnsonBound.e B' v / n)^2) := by
            simp [JohnsonDenominator, q, frac, mul_div_assoc]
            ring

          -- 2. Cancel frac.
          have term_simplification : (frac * (JohnsonBound.d B') / (n : ℚ)) /
              JohnsonDenominator B' v =
              (JohnsonBound.d B' / n) /
              (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
              frac * (JohnsonBound.e B' v / n)^2) := by
            set D : ℚ :=
              JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                frac * (JohnsonBound.e B' v / n) ^ 2
            calc
              (frac * JohnsonBound.d B' / (n : ℚ)) / JohnsonDenominator B' v
                  = (frac * (JohnsonBound.d B' / n)) / JohnsonDenominator B' v := by
                      simp [mul_div_assoc]
              _ = (frac * (JohnsonBound.d B' / n)) / (frac * D) := by
                      simp [denom_expansion, D]
              _ = (JohnsonBound.d B' / n) / D := by
                      simpa [D] using
                        (mul_div_mul_left (a := JohnsonBound.d B' / n) (b := D)
                          (c := frac) hfrac_ne)

          -- 3. Bound eB' by e.
          have e_ineq : JohnsonBound.e B' v ≤ e := by
            have hB'_pos : 0 < B'.card := by
              have hB'_ge2 : 2 ≤ B'.card := by
                exact le_of_not_gt h_size
              omega
            have hsum_le :
                ∑ x ∈ B', (Δ₀(v, x) : ℚ) ≤ ∑ x ∈ B', (e : ℚ) := by
              refine Finset.sum_le_sum ?_
              intro x hx
              have hx' : Δ₀(v, x) ≤ e := by
                have hx' : Δ₀(x, v) ≤ e := by
                  have hx' : x ∈ B ∧ Δ₀(x, v) ≤ e := by
                    simpa [B'] using hx
                  exact hx'.2
                simpa [hammingDist_comm] using hx'
              exact_mod_cast hx'
            have hsum_le' :
                ∑ x ∈ B', (Δ₀(v, x) : ℚ) ≤ (e : ℚ) * B'.card := by
              calc
                ∑ x ∈ B', (Δ₀(v, x) : ℚ)
                    ≤ ∑ x ∈ B', (e : ℚ) := hsum_le
                _ = (e : ℚ) * B'.card := by
                    simp [Finset.sum_const, mul_comm]
            have hB'_pos_q : (0 : ℚ) < B'.card := by
              exact_mod_cast hB'_pos
            have hdiv_le :
                (∑ x ∈ B', (Δ₀(v, x) : ℚ)) / B'.card ≤ (e : ℚ) := by
              exact (div_le_iff₀ hB'_pos_q).2 (by
                simpa [mul_comm] using hsum_le')
            have h_e :
                JohnsonBound.e B' v =
                  (∑ x ∈ B', (Δ₀(v, x) : ℚ)) / B'.card := by
              simp [JohnsonBound.e, div_eq_mul_inv, mul_comm]
            simpa [h_e] using hdiv_le

          -- 4. Bound dB' by d.
          have d_ineq : (d : ℚ) ≤ JohnsonBound.d B' := by
            simp[hd_le_dB']

          -- 5. Compare worst-case values (monotone).
          have worst_case_bound : (JohnsonBound.d B' / n) /
              (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
              frac * (JohnsonBound.e B' v / n)^2) ≤
              (d / n) / (d / n - 2 * e / n + frac * (e / n)^2) := by
            set D1 : ℚ := JohnsonBound.d B' / n
            set E1 : ℚ := JohnsonBound.e B' v / n
            have hfrac_ge : (1 : ℚ) ≤ frac := by
              exact le_of_lt hfrac_gt1
            have hD : D0 ≤ D1 := by
              simpa [D0, D1] using (div_le_div_of_nonneg_right d_ineq hn_nonneg)
            have hE : E1 ≤ E0 := by
              simpa [E1, E0] using (div_le_div_of_nonneg_right e_ineq hn_nonneg)
            have h_sqrt_ge :
                (n : ℝ) - d ≤ Real.sqrt ((n * (n - d)) : ℝ) := by
              have h_nd_nonneg : (0 : ℝ) ≤ (n : ℝ) - d := by
                exact sub_nonneg.mpr (by exact_mod_cast d_le_n)
              have h_nd_le_n : (n : ℝ) - d ≤ (n : ℝ) := by linarith
              have h_sq : ((n : ℝ) - d) ^ 2 ≤ (n : ℝ) * (n - d) := by
                have hmul := mul_le_mul_of_nonneg_right h_nd_le_n h_nd_nonneg
                simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
              exact Real.le_sqrt_of_sq_le h_sq
            have h_e_le_d_real : (e : ℝ) ≤ d := by
              linarith [h, h_sqrt_ge]
            have h_e_le_d : (e : ℚ) ≤ (d : ℚ) := by
              exact_mod_cast h_e_le_d_real
            have hE0_le_D0 : E0 ≤ D0 := by
              simpa [E0, D0] using (div_le_div_of_nonneg_right h_e_le_d hn_nonneg)
            have hD0_le_one_frac : D0 ≤ 1 / frac := by
              have hmul : D0 * frac ≤ 1 := by
                have h' : frac * (d / n : ℚ) ≤ 1 := by
                  exact le_of_not_gt h_d_close_n
                simpa [D0, mul_comm] using h'
              exact (le_div_iff₀ hfrac_pos).2 (by simpa using hmul)
            have hE0_le_one_frac : E0 ≤ 1 / frac := by
              exact le_trans hE0_le_D0 hD0_le_one_frac
            have hE1_le_one_frac : E1 ≤ 1 / frac := by
              exact le_trans hE hE0_le_one_frac
            have hE0_nonneg : (0 : ℚ) ≤ E0 := by
              have hE0_nonneg_nat : (0 : ℚ) ≤ (e : ℚ) := by
                exact_mod_cast (Nat.zero_le e)
              exact div_nonneg hE0_nonneg_nat hn_nonneg
            have hsum_nonneg :
                (0 : ℚ) ≤ ∑ x ∈ B', (Δ₀(v, x) : ℚ) := by
              refine Finset.sum_nonneg ?_
              intro x hx
              exact_mod_cast (Nat.cast_nonneg (Δ₀(v, x)))
            have hE_nonneg : (0 : ℚ) ≤ JohnsonBound.e B' v := by
              have hB'_nonneg : (0 : ℚ) ≤ (B'.card : ℚ) := by
                exact_mod_cast (Nat.cast_nonneg B'.card)
              have hB'_inv_nonneg : (0 : ℚ) ≤ (1 : ℚ) / B'.card := by
                exact div_nonneg (show (0 : ℚ) ≤ (1 : ℚ) by norm_num) hB'_nonneg
              simpa [JohnsonBound.e, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
                (mul_nonneg hB'_inv_nonneg hsum_nonneg)
            have hE1_nonneg : (0 : ℚ) ≤ E1 := by
              exact div_nonneg hE_nonneg hn_nonneg

            have hden1_pos : (0 : ℚ) <
                D1 - 2 * E1 + frac * E1 ^ 2 := by
              have hdenJ :
                  (0 : ℚ) < JohnsonDenominator B' v := by
                exact (johnson_condition_strong_iff_johnson_denom_pos).1 h_johnson_strong
              have hdenJ' :
                  (0 : ℚ) <
                    frac * (JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                    frac * (JohnsonBound.e B' v / n) ^ 2) := by
                simpa [denom_expansion] using hdenJ
              have hdenJ'' :
                  (0 : ℚ) <
                    JohnsonBound.d B' / n - 2 * JohnsonBound.e B' v / n +
                    frac * (JohnsonBound.e B' v / n) ^ 2 := by
                rcases (mul_pos_iff.mp hdenJ') with hpos | hneg
                · exact hpos.2
                · exfalso
                  linarith [hneg.1, hfrac_pos]
              simpa [D1, E1, mul_div_assoc] using hdenJ''

            have hden0_nonneg :
                (0 : ℚ) ≤ D0 - 2 * E0 + E0 ^ 2 := by
              exact quad_nonneg
            have hden0_pos :
                (0 : ℚ) < D0 - 2 * E0 + frac * E0 ^ 2 := by
              have h_expand :
                  D0 - 2 * E0 + frac * E0 ^ 2 =
                    (D0 - 2 * E0 + E0 ^ 2) + (frac - 1) * E0 ^ 2 := by
                ring
              by_cases hE0_zero : E0 = 0
              · have hd_pos : (0 : ℚ) < (d : ℚ) := by
                  exact_mod_cast (Nat.succ_le_iff).1 d_not_small
                have hD0_pos : (0 : ℚ) < D0 := by
                  simpa [D0] using (div_pos hd_pos hn_pos)
                simpa [h_expand, hE0_zero] using hD0_pos
              · have hE0_sq_pos : (0 : ℚ) < E0 ^ 2 := by
                  have hE0_sq_pos' : (0 : ℚ) < E0 * E0 := by
                    exact mul_self_pos.mpr hE0_zero
                  simpa [pow_two] using hE0_sq_pos'
                have hfrac1_pos : (0 : ℚ) < frac - 1 := by
                  linarith [hfrac_gt1]
                have hterm_pos :
                    (0 : ℚ) < (frac - 1) * E0 ^ 2 := by
                  exact mul_pos hfrac1_pos hE0_sq_pos
                have hden0_pos' :
                    (0 : ℚ) <
                      (D0 - 2 * E0 + E0 ^ 2) + (frac - 1) * E0 ^ 2 := by
                  linarith [hden0_nonneg, hterm_pos]
                simpa [h_expand] using hden0_pos'

            have hE_sum : E0 + E1 ≤ 2 / frac := by
              calc
                E0 + E1 ≤ (1 / frac) + (1 / frac) := by
                  linarith [hE0_le_one_frac, hE1_le_one_frac]
                _ = 2 / frac := by ring
            have h_gmono :
                D0 - 2 * E1 + frac * E1 ^ 2 ≥ D0 - 2 * E0 + frac * E0 ^ 2 := by
              have h1 : (0 : ℚ) ≤ E0 - E1 := by linarith [hE]
              have h2 : (0 : ℚ) ≤ 2 - frac * (E0 + E1) := by
                have hmul :
                    frac * (E0 + E1) ≤ 2 := by
                  have h := mul_le_mul_of_nonneg_left hE_sum (le_of_lt hfrac_pos)
                  have hfrac_ne : (frac : ℚ) ≠ 0 := by exact ne_of_gt hfrac_pos
                  have hright : frac * (2 / frac) = (2 : ℚ) := by
                    field_simp [hfrac_ne]
                  simpa [hright] using h
                linarith [hmul]
              have hdiff :
                  (0 : ℚ) ≤ (E0 - E1) * (2 - frac * (E0 + E1)) := by
                exact mul_nonneg h1 h2
              have hfactor :
                  (D0 - 2 * E1 + frac * E1 ^ 2) - (D0 - 2 * E0 + frac * E0 ^ 2) =
                    (E0 - E1) * (2 - frac * (E0 + E1)) := by
                ring
              have hdiff' :
                  (0 : ℚ) ≤
                    (D0 - 2 * E1 + frac * E1 ^ 2) - (D0 - 2 * E0 + frac * E0 ^ 2) := by
                simpa [hfactor] using hdiff
              linarith [hdiff']
            have hden0_pos' :
                (0 : ℚ) < D0 - 2 * E1 + frac * E1 ^ 2 := by
              exact lt_of_lt_of_le hden0_pos h_gmono

            have hC_nonneg :
                (0 : ℚ) ≤ 2 * E1 - frac * E1 ^ 2 := by
              have hmul :
                  frac * E1 ≤ 1 := by
                have h := mul_le_mul_of_nonneg_left hE1_le_one_frac (le_of_lt hfrac_pos)
                have hfrac_ne : (frac : ℚ) ≠ 0 := by exact ne_of_gt hfrac_pos
                have hright : frac * frac⁻¹ = (1 : ℚ) := by
                  field_simp [hfrac_ne]
                simpa [div_eq_mul_inv, hright, mul_assoc] using h
              have h2 : (0 : ℚ) ≤ 2 - frac * E1 := by
                linarith [hmul]
              have hprod : (0 : ℚ) ≤ E1 * (2 - frac * E1) := by
                exact mul_nonneg hE1_nonneg h2
              have hfactor : E1 * (2 - frac * E1) = 2 * E1 - frac * E1 ^ 2 := by
                ring
              simpa [hfactor] using hprod

            have hstep1 :
                D1 / (D1 - 2 * E1 + frac * E1 ^ 2) ≤
                D0 / (D0 - 2 * E1 + frac * E1 ^ 2) := by
              have hmul :
                  D1 * (D0 - 2 * E1 + frac * E1 ^ 2) ≤
                  D0 * (D1 - 2 * E1 + frac * E1 ^ 2) := by
                have h : (0 : ℚ) ≤ (D1 - D0) := by linarith [hD]
                have h' : (0 : ℚ) ≤ (2 * E1 - frac * E1 ^ 2) := hC_nonneg
                nlinarith [h, h']
              exact (div_le_div_iff₀ hden1_pos hden0_pos').2 hmul
            have hstep2 :
                D0 / (D0 - 2 * E1 + frac * E1 ^ 2) ≤
                D0 / (D0 - 2 * E0 + frac * E0 ^ 2) := by
              have hmul :
                  D0 * (D0 - 2 * E0 + frac * E0 ^ 2) ≤
                  D0 * (D0 - 2 * E1 + frac * E1 ^ 2) := by
                have hD0_nonneg : (0 : ℚ) ≤ D0 := by
                  have hd0 : (0 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (Nat.zero_le d)
                  exact div_nonneg hd0 hn_nonneg
                exact mul_le_mul_of_nonneg_left h_gmono hD0_nonneg
              exact (div_le_div_iff₀ hden0_pos' hden0_pos).2 hmul
            have hfinal :
                D1 / (D1 - 2 * E1 + frac * E1 ^ 2) ≤
                D0 / (D0 - 2 * E0 + frac * E0 ^ 2) := by
              exact le_trans hstep1 hstep2
            simpa [D0, D1, E0, E1, mul_div_assoc] using hfinal

          -- 6. Final algebraic bound.
          have final_calc : (d / n) / (d / n - 2 * e / n + frac * (e / n)^2) ≤
              q * d * n := by
            have hfrac1_pos : (0 : ℚ) < frac - 1 := by linarith [hfrac_gt1]
            have hbase_nonneg : (0 : ℚ) ≤ D0 - 2 * E0 + E0 ^ 2 := by
              exact quad_nonneg
            have hden_lb : (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤ Den := by
              by_cases he0 : e = 0
              · subst he0
                have hD0_ge : (1 : ℚ) / n ≤ D0 := by
                  have hd_ge1 : (1 : ℚ) ≤ (d : ℚ) := by exact_mod_cast d_not_small
                  exact (div_le_div_of_nonneg_right hd_ge1 hn_nonneg)
                have hmul : (n : ℚ) ≤ q * (n : ℚ) ^ 2 := by
                  have hq_ge1 : (1 : ℚ) ≤ q := by linarith [q_not_small]
                  have hn_ge1 : (1 : ℚ) ≤ n := by exact_mod_cast n_not_small
                  calc
                    (n : ℚ) ≤ (n : ℚ) * (n : ℚ) := by nlinarith [hn_ge1]
                    _ ≤ q * (n : ℚ) * (n : ℚ) := by
                      have hnn_nonneg : (0 : ℚ) ≤ (n : ℚ) * (n : ℚ) := by
                        exact mul_nonneg (le_of_lt hn_pos) (le_of_lt hn_pos)
                      simpa [mul_comm, mul_left_comm, mul_assoc] using
                        (mul_le_mul_of_nonneg_right hq_ge1 hnn_nonneg)
                    _ = q * (n : ℚ) ^ 2 := by ring
                have hpos1 : (0 : ℚ) < q * (n : ℚ) ^ 2 := by
                  exact mul_pos hq_pos hn2_pos
                have hpos2 : (0 : ℚ) < (n : ℚ) := hn_pos
                have h1 : (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤ (1 : ℚ) / n := by
                  exact (div_le_div_iff₀ hpos1 hpos2).2 (by simpa using hmul)
                have hden : (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤ D0 :=
                  le_trans h1 hD0_ge
                simpa [D0, E0, Den] using hden
              · have he_pos_nat : 0 < e := Nat.pos_of_ne_zero he0
                have he_pos : (0 : ℚ) < (e : ℚ) := by exact_mod_cast he_pos_nat
                have hE0_pos : (0 : ℚ) < E0 := by exact div_pos he_pos hn_pos
                have hE0_ge : (1 : ℚ) / n ≤ E0 := by
                  have he_ge1 : (1 : ℚ) ≤ (e : ℚ) := by
                    exact_mod_cast (Nat.succ_le_iff).2 he_pos_nat
                  exact (div_le_div_of_nonneg_right he_ge1 hn_nonneg)
                have hE0_sq_ge : (1 : ℚ) / (n : ℚ) ^ 2 ≤ E0 ^ 2 := by
                  have h1 : (0 : ℚ) ≤ (1 : ℚ) / n := by
                    exact div_nonneg (by norm_num) hn_nonneg
                  have h := mul_self_le_mul_self h1 hE0_ge
                  simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
                have h_expand : Den = (D0 - 2 * E0 + E0 ^ 2) + (frac - 1) * E0 ^ 2 := by
                  ring
                have hden_ge :
                    (frac - 1) * E0 ^ 2 ≤ Den := by
                  have htmp :
                      (frac - 1) * E0 ^ 2 ≤
                        (D0 - 2 * E0 + E0 ^ 2) + (frac - 1) * E0 ^ 2 := by
                    linarith [hbase_nonneg]
                  simpa [h_expand] using htmp
                have hden_ge' : (frac - 1) / (n : ℚ) ^ 2 ≤ Den := by
                  have h1 :
                      (frac - 1) * ((1 : ℚ) / (n : ℚ) ^ 2) ≤
                        (frac - 1) * E0 ^ 2 := by
                    exact mul_le_mul_of_nonneg_left hE0_sq_ge (le_of_lt hfrac1_pos)
                  have h1' :
                      (frac - 1) / (n : ℚ) ^ 2 =
                        (frac - 1) * ((1 : ℚ) / (n : ℚ) ^ 2) := by
                    simp [div_eq_mul_inv]
                  exact le_trans (by simpa [h1'] using h1) hden_ge
                have hfrac1_ge' :
                    (1 : ℚ) / (q * (n : ℚ) ^ 2) ≤ (frac - 1) / (n : ℚ) ^ 2 := by
                  have h1 := div_le_div_of_nonneg_right one_div_q_le hn2_nonneg
                  have h1' : (1 : ℚ) / (q * (n : ℚ) ^ 2) = (1 : ℚ) / q / (n : ℚ) ^ 2 := by
                    field_simp [hq_ne]
                  simpa [h1'] using h1
                exact le_trans hfrac1_ge' hden_ge'
            have hnum_nonneg : (0 : ℚ) ≤ d / n := by
              have hd0 : (0 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (Nat.zero_le d)
              exact div_nonneg hd0 hn_nonneg
            have hden_pos : (0 : ℚ) < (1 : ℚ) / (q * (n : ℚ) ^ 2) := by
              have hpos : (0 : ℚ) < q * (n : ℚ) ^ 2 := by
                exact mul_pos hq_pos hn2_pos
              exact one_div_pos.mpr hpos
            have hstep :
                (d / n) / Den ≤ (d / n) / ((1 : ℚ) / (q * (n : ℚ) ^ 2)) := by
              exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_lb
            calc
              (d / n) / (d / n - 2 * e / n + frac * (e / n) ^ 2)
                  = (d / n) / Den := by simp [Den, D0, E0, mul_div_assoc]
              _ ≤ (d / n) / ((1 : ℚ) / (q * (n : ℚ) ^ 2)) := hstep
              _ = q * d * n := by
                    field_simp [hq_ne, hn_pos.ne']
                    ring

          -- Combine the steps.
          rw [term_simplification]
          apply le_trans worst_case_bound
          exact final_calc

        exact le_trans current_bound last_bound

end JohnsonBound
