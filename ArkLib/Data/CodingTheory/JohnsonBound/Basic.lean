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
    intro d q frac _
    let B' := B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)

    by_cases h_size : B'.card < 2
    -- trivial case
    ·
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

      have qdn_not_small : (q * d * n) ≥ 2 := by
        have hdq : (d : ℚ) ≥ (1 : ℚ) := by exact_mod_cast d_not_small
        have hnq : (n : ℚ) ≥ (1 : ℚ) := by exact_mod_cast n_not_small
        have dn_ge_one : (d : ℚ) * (n : ℚ) ≥ (1 : ℚ) := by nlinarith [hdq, hnq]
        have : q * ((d : ℚ) * (n : ℚ)) ≥ (2 : ℚ) := by nlinarith [q_not_small, dn_ge_one]
        simpa [mul_assoc] using this

      have hcard_nat : B'.card ≤ 1 := by exact Nat.le_of_lt_succ h_size

      have hcard : (B'.card : ℚ) ≤ (1 : ℚ) := by exact_mod_cast hcard_nat

      have rhs_ge_two : (2 : ℚ) ≤ q * (d : ℚ) * (n : ℚ) := by simpa [mul_assoc] using qdn_not_small

      have rhs_ge_one : (1 : ℚ) ≤ q * (d : ℚ) * (n : ℚ) :=
        le_trans (by norm_num : (1 : ℚ) ≤ 2) rhs_ge_two

      exact le_trans hcard rhs_ge_one
    -- non-trivial case
    ·
      have h_johnson_strong : JohnsonConditionStrong B' v := by
        have h_johnson_weak : JohnsonConditionWeak B e := by
          sorry
        have h_size' : 1 < B'.card := by
          omega
        have hF_nontriv : (2 : ℕ) ≤ Fintype.card F := by
          classical
          have : 1 < Fintype.card F := by
            simpa [Fintype.one_lt_card_iff] using (⟨(0:F), (1:F), by simp⟩ : ∃ a b : F, a ≠ b)
          omega
        exact johnson_condition_weak_implies_strong h_johnson_weak h_size' hF_nontriv

      have johnson_result := johnson_bound h_johnson_strong

      have current_bound :
          (B'.card : ℚ) ≤
          frac * (JohnsonBound.d B') / (n : ℚ) / JohnsonDenominator B' v := by
        simpa using johnson_result

      have last_bound :
          frac * (JohnsonBound.d B') / (n : ℚ) / JohnsonDenominator B' v ≤
          q * (d : ℚ) * (n : ℚ) := by
        sorry

      linarith

end JohnsonBound
