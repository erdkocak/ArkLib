/-
Copyright (c) 2024 - 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Chung Thai Nguyen, Quang Dao
-/
import ArkLib.Data.Nat.Bitwise
import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ProximityGap -- Assuming BCIKS20 results are here or accessible
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import ArkLib.Data.Probability.Notation
import ArkLib.Data.CodingTheory.Prelims
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Defs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.Henselian
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.ENNReal.Inv

/-!
# Proximity Gaps in Interleaved Codes

This file formalizes the main results from the paper "Proximity Gaps in Interleaved Codes"
by Diamond and Gruen (DG25).

## Main Definitions

The core results from DG25 are the following:
1. `affine_gaps_lifted_to_interleaved_codes`: **Theorem 3.1 (DG25):** If a linear code `C` has
  proximity gaps for affine lines (up to unique decoding radius), then its interleavings `C^m`
  also do.
2. `interleaved_affine_gaps_imply_tensor_gaps`: **Theorem 3.6 (AER24):** If all interleavings `C^m`
  have proximity gaps for affine lines, then `C` exhibits tensor-style proximity gaps.
3. `reedSolomon_tensorStyleProximityGap`:  **Corollary 3.7 (DG25):** Reed-Solomon codes exhibit
  tensor-style proximity gaps (up to unique decoding radius).

This formalization assumes the availability of Theorem 2.2 (Ben+23 / BCIKS20 Thm 4.1) stating
that Reed-Solomon codes have proximity gaps for affine lines up to the unique decoding radius.

## TODOs
- Nontrivial of RS code
- Proximity gaps for affine lines of RS code (Theorem 4.1 BCIKS20)
- Conjecture 4.3 proposes ε=n might hold for general linear codes.
- Generalize the theorems to using real numbers?

## References

- [DG25] Benjamin E. Diamond and Angus Gruen. “Proximity Gaps in Interleaved Codes”. In: IACR
Communications in Cryptology 1.4 (Jan. 13, 2025). issn: 3006-5496. doi: 10.62056/a0ljbkrz.

- [AER24] Guillermo Angeris, Alex Evans, and Gyumin Roh. A Note on Ligero and Logarithmic
  Randomness. Cryptology ePrint Archive, Paper 2024/1399. 2024. url: https://eprint.iacr.org/2024/1399.
-/

noncomputable section

open Code LinearCode InterleavedCode ReedSolomonCode ProximityGap ProbabilityTheory Filter Finset
open NNReal Finset Function
open scoped BigOperators LinearCode ProbabilityTheory
open Real

section SimplePrelims
lemma Nat.cast_gt_Real_one (a : ℕ) (ha : a > 1) : (a : ℝ) > 1 := by
  rw [gt_iff_lt]
  have h := Nat.cast_lt (α := ℝ) (m := 1) (n := a).mpr
  rw [cast_one] at h
  exact h ha

lemma Nat.sub_div_two_add_one_le (n k : ℕ) [NeZero n] [NeZero k] (hkn : k ≤ n) :
    (n - k) / 2 + 1 ≤ n := by
  have h_div_le_self : (n - k) / 2 ≤ n - k := Nat.div_le_self (n - k) 2
  have h_le_sub_add_one : (n - k) / 2 + 1 ≤ n - k + 1 := by
    apply Nat.add_le_add_right h_div_le_self 1
  have h_sub_lt_n : n - k < n := by
    apply Nat.sub_lt_self
    · exact NeZero.pos k
    · exact hkn
  have h_sub_add_one_le_n : n - k + 1 ≤ n := Nat.succ_le_of_lt h_sub_lt_n
  exact le_trans h_le_sub_add_one h_sub_add_one_le_n

/-- (h : a → b) → (a ∧ b) = a -/
lemma conj_right_eq_self_of_imp {a b : Prop} (h : a → b) : (a ∧ b) = a := by
  simp only [eq_iff_iff, and_iff_left_iff_imp]
  exact h

def initRandomnessFun {F : Type*} [Fintype F] [Nonempty F] {ϑ : ℕ} (hϑ : ϑ > 0)
    (r : Fin ϑ → F) : Fin (ϑ - 1) → F := Fin.init (n := ϑ - 1) (α :=
  fun _ => F) (q := fun j => r ⟨j, by omega⟩)

def equivFinFunSplitLast {F : Type*} [Fintype F] [Nonempty F] {ϑ : ℕ} :
    (Fin (ϑ + 1) → F) ≃ (F × (Fin ϑ → F)) where
  toFun := fun r => (r (Fin.last ϑ), Fin.init r)
  invFun := fun (r_last, r_init) => Fin.snoc r_init r_last
  left_inv := by
    simp only
    intro r
    ext i
    simp only [Fin.snoc_init_self]
  right_inv := by
    simp only
    intro (r_last, r_init)
    ext i
    · simp only [Fin.snoc_last]
    · simp only [Fin.init_snoc]
end SimplePrelims

section ENNReal
open ENNReal
variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}
-- Reference: `FormulaRabbit81`'s PR: https://github.com/leanprover-community/mathlib4/commit/2452ad7288de553bc1201969ed13782affaf3459

lemma ENNReal.div_lt_div_iff_left (hc₀ : c ≠ 0) (hc : c ≠ ∞) : a / c < b / c ↔ a < b :=
  ENNReal.mul_lt_mul_right (by simpa) (by simpa)

@[gcongr]
lemma ENNReal.div_lt_div_right (hc₀ : c ≠ 0) (hc : c ≠ ∞) (hab : a < b) : a / c < b / c :=
  (ENNReal.div_lt_div_iff_left hc₀ hc).2 hab

theorem ENNReal.mul_inv_rev_ENNReal {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ((a : ENNReal)⁻¹ * (b : ENNReal)⁻¹) = ((a : ENNReal) * (b : ENNReal))⁻¹ := by
-- Let x = ↑a and y = ↑b for readability
  let x : ENNReal := a
  let y : ENNReal := b
  -- Prove x and y are non-zero and finite (needed for inv_cancel)
  have hx_ne_zero : x ≠ 0 := by exact Nat.cast_ne_zero.mpr ha
  have hy_ne_zero : y ≠ 0 := by exact Nat.cast_ne_zero.mpr hb
  have hx_ne_top : x ≠ ∞ := by exact ENNReal.natCast_ne_top a
  have hy_ne_top : y ≠ ∞ := by exact ENNReal.natCast_ne_top b
  have ha_NNReal_ne0 : (a : ℝ≥0) ≠ 0 := by exact Nat.cast_ne_zero.mpr ha
  have hb_NNReal_ne0 : (b : ℝ≥0) ≠ 0 := by exact Nat.cast_ne_zero.mpr hb
  -- (a * b)⁻¹ = b⁻¹ * a⁻¹
  have hlhs : ((a : ENNReal)⁻¹ * (b : ENNReal)⁻¹) = ((a : ℝ≥0)⁻¹ * (b : ℝ≥0)⁻¹) := by
    rw [coe_inv (hr := by exact ha_NNReal_ne0)]
    rw [coe_inv (hr := by exact hb_NNReal_ne0)]
    rw [ENNReal.coe_natCast, ENNReal.coe_natCast]
  have hrhs : ((a : ENNReal) * (b : ENNReal))⁻¹ = ((a : ℝ≥0) * (b : ℝ≥0))⁻¹ := by
    rw [coe_inv (hr := (mul_ne_zero_iff_right hb_NNReal_ne0).mpr (ha_NNReal_ne0))]
    simp only [coe_mul, coe_natCast]
  rw [hlhs, hrhs]
  rw [mul_inv_rev (a := (a : ℝ≥0)) (b := (b : ℝ≥0))]
  rw [coe_mul, mul_comm]
end ENNReal

section ProbabilityTools
/-- Unrolls `Pr_{ let x ← D }[P x]` into a sum of the form
`∑' x, Pr[x] * (if P x then 1 else 0)`. -/
theorem prob_tsum_form_singleton {α : Type} (D : PMF α) (P : α → Prop) [DecidablePred P] :
    Pr_{ let x ← D }[P x] = ∑' x, (D x) * (if P x then 1 else 0) := by
  -- Expand Pr_ using the same approach as Notation.lean
  simp only [Bind.bind, PMF.bind, pure, PMF.pure_apply, eq_iff_iff, mul_ite, mul_one, mul_zero]
  simp only [DFunLike.coe]
  have h: ∀ a: α, (True = P a) = (P a) := fun a => by
    if h_P_a: P a then
      simp only [h_P_a]
    else
      simp only [h_P_a, eq_iff_iff, iff_false, not_true_eq_false]
  simp_rw [h]

theorem prob_tsum_form_split_first {α : Type} (D : PMF α) (D_rest : α → PMF Prop) :
    (do let x ← D; D_rest x) True = ∑' x, (D x) * (D_rest x True) := by
  -- These are definitionally the same!
  exact PMF.bind_apply D D_rest True

open Classical in
/-- Unrolls `Pr_{ let x ← D; let y ← D }[P x y]` into a sum of the form
`∑' (x × y), (if P x y then 1 else 0)`. -/
theorem prob_tsum_form_doubleton {α β : Type}
    (D₁ : PMF α) (D₂ : PMF β)
    (P : α → β → Prop) [∀ x, DecidablePred (P x)] : -- Need decidability for inner P
    Pr_{ let x ← D₁; let y ← D₂ }[P x y]
    =  ∑' xy : α × β, (D₁ xy.1) * (D₂ xy.2) * (if P xy.1 xy.2 then (1 : ENNReal) else 0) := by
  let D_rest := fun (x : α) => (do
    let y ← D₂
    return (P x y)
  )
  conv_lhs =>
    apply prob_tsum_form_split_first (D := D₁) (D_rest := D_rest)
  simp_rw [D_rest]
  simp_rw [prob_tsum_form_singleton]
  conv_lhs => enter [1, x]; rw [←ENNReal.tsum_mul_left]
  -- ⊢ (∑' (x : α), ... = ∑' (x : γ) (i : δ), ...
  rw [←ENNReal.tsum_prod]
  congr 1
  funext xy
  rw [←mul_assoc]

theorem prob_uniform_eq_card_filter_div_card {F : Type} [Fintype F] [Nonempty F]
    (P : F → Prop) [DecidablePred P] :
  Pr_{ let r ←$ᵖ F }[ P r ] =
    ((Finset.filter (α := F) P Finset.univ).card : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  classical
  -- Expand Pr_ using the same approach as Notation.lean
  simp only [Bind.bind, PMF.bind, PMF.uniformOfFintype_apply, pure, PMF.pure_apply, eq_iff_iff,
    mul_ite, mul_one, mul_zero, ENNReal.coe_natCast]
  simp only [DFunLike.coe, true_iff]
  -- ⊢ (∑' (a : F), if P a then (↑(Fintype.card F))⁻¹ else 0)
    -- = ↑(#(filter P univ)) / ↑(Fintype.card F)
  rw [tsum_eq_sum (α := ENNReal) (β := F) (f := fun a => if P a then (↑(Fintype.card F))⁻¹ else 0)
    (s := Finset.filter P Finset.univ) (hf := fun b => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hb
    simp only [hb, if_false]
  )] -- rewrite the infinite sum as a sum
  -- ⊢ (∑ b with P b, if P b then (↑(Fintype.card F))⁻¹ else 0) = ↑(#(filter P univ)) / ↑q
  rw [Finset.sum_ite] -- simplify the if-then-else inside the sum
  simp only [Finset.sum_const_zero, add_zero] -- remove the second sum of 0s
  rw [Finset.sum_const] -- simplify the left sum of the constants
  -- Rewrite nsmul (scalar multiplication by ℕ) as standard multiplication using Nat.cast
  rw [nsmul_eq_mul'] -- Use nsmul_eq_mul' which handles the coercion to ℝ≥0
  -- ⊢ (↑(Fintype.card F))⁻¹ * ↑(#({x ∈ filter P univ | P x})) = ↑(#(filter P univ)) / ↑q
  rw [mul_comm]
  conv_lhs => rw [←div_eq_mul_inv]
  -- ⊢ ↑(#({x ∈ filter P univ | P x})) / ↑(Fintype.card F) = ↑(#(filter P univ)) / ↑(Fintype.card F)
  have h_card_eq: {x ∈ filter P univ | P x} = filter P univ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- ⊢ P x ∧ P x ↔ P x
    rw [and_self_iff]
  rw [h_card_eq]

lemma Fintype.card_fun_fin_one_eq {F : Type} [Fintype F] [Nonempty F] :
  Fintype.card (Fin 1 → F) = Fintype.card F := by
  rw [Fintype.card_fun]
  simp only [Fintype.card_unique, pow_one]

theorem prob_uniform_singleton_finFun_eq {F : Type} [Fintype F] [Nonempty F]
    (P : F → Prop) [DecidablePred P] :
  Pr_{ let r ← $ᵖ (Fin 1 → F) }[
    P (r 0) ] = Pr_{ let r ←$ᵖ F }[ P r ] := by
-- 1. Unfold both sides using the definition of probability for uniform distributions
  rw [prob_uniform_eq_card_filter_div_card (F := F)]
  rw [prob_uniform_eq_card_filter_div_card (F := Fin 1 → F)]
  -- 2. Handle the denominators: Show card(F) = card(Fin 1 → F)
  -- Fintype.card_fun_fin_one proves that `Fintype.card (Fin 1 → F) = Fintype.card F`
  rw [Fintype.card_fun_fin_one_eq]
  -- 3. Handle the numerators: Show the cardinalities of the two filter sets are equal.
  congr 1 -- This tells Lean the denominators match, so just prove the numerators are equal
  -- Define the equivalence `e` that maps `(r : Fin 1 → F)` to `r 0`
  let e : (Fin 1 → F) ≃ F := Equiv.funUnique (Fin 1) F
  -- Define the two sets we are comparing
  let s₁ := Finset.filter (fun (r : Fin 1 → F) => P (r 0)) Finset.univ
  let s₂ := Finset.filter P Finset.univ
  -- Show that s₂ is just the image of s₁ under the map `e`
  have h_map_eq : s₂ = Finset.map e.toEmbedding s₁ := by
    ext x -- ⊢ x ∈ s₂ ↔ x ∈ Finset.map e.toEmbedding s₁
    simp only [mem_filter, mem_univ, true_and, Fin.isValue, mem_map_equiv, s₂, s₁]
    -- ⊢ P x ↔ P (e.symm x 0)
    rfl
  simp only [ENNReal.coe_natCast, Fin.isValue, Nat.cast_inj]
  have h_card_eq : s₂.card = s₁.card := by
    rw [h_map_eq]
    rw [Finset.card_map e.toEmbedding]
  rw [h_card_eq]

theorem prob_split_uniform_sampling_of_prod {γ δ : Type}
    -- Fintype & Nonempty assumptions for all types
    [Fintype γ] [Fintype δ] [Nonempty γ] [Nonempty δ]
    -- The predicate on the original (combined) type
    (P : γ × δ → Prop)
    -- Decidability for the predicates
    [DecidablePred P]
    [DecidablePred (fun xy : γ × δ => P xy)] :
    -- LHS: Probability over the combined space
    Pr_{ let r ← $ᵖ (γ × δ) }[ P r ] =
    -- RHS: Probability over the sequential, split spaces
    Pr_{ let x ← $ᵖ γ; let y ← $ᵖ δ }[ P (x, y) ] := by
  rw [prob_tsum_form_singleton]
  let D_rest := fun (x : γ) => (do
    let y ← $ᵖ δ
    return (P (x, y))
  )
  conv_rhs =>
    apply prob_tsum_form_split_first (D := $ᵖ γ) (D_rest := D_rest)
  simp_rw [D_rest]
  simp_rw [prob_tsum_form_singleton]
  conv_rhs => enter [1, x]; rw [←ENNReal.tsum_mul_left]
  rw [←ENNReal.tsum_prod]
  congr
  funext xy
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul, mul_ite, mul_one,
    mul_zero, Prod.mk.eta]
  by_cases hP : P xy
  · simp only [hP, ↓reduceIte]
    rw [ENNReal.mul_inv_rev_ENNReal (ha := Fintype.card_ne_zero) (hb := Fintype.card_ne_zero)]
  · simp only [hP, ↓reduceIte]

/--
Proves that a `do` block sampling two independent uniform distributions
is equal to the single uniform distribution over the product type.
-/
theorem do_two_uniform_sampling_eq_uniform_prod {α β : Type} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] :
    (do
      let x ← $ᵖ α;
      let y ← $ᵖ β
      pure (x, y)
    ) = $ᵖ (α × β) := by
  apply PMF.ext
  intro xy
  rcases xy with ⟨x, y⟩
  have h_rhs : ($ᵖ (α × β)) (x, y) = (Fintype.card (α × β) : ENNReal)⁻¹ := by
    rw [PMF.uniformOfFintype_apply]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  dsimp only [Bind.bind, PMF.bind_apply]
  simp only [PMF.uniformOfFintype_apply]
  rw [ENNReal.tsum_mul_left]
  rw [←ENNReal.tsum_prod]
  rw [ENNReal.tsum_mul_left]
  rw [←mul_assoc]
  rw [ENNReal.mul_inv_rev_ENNReal (ha := Fintype.card_ne_zero) (hb := Fintype.card_ne_zero)]
  conv_rhs =>
    rw [←mul_one (a := ((Fintype.card α : ENNReal) *  (Fintype.card β : ENNReal) : ENNReal)⁻¹)]
  congr 1
  simp only [Prod.mk.eta]
  dsimp only [pure, PMF.pure_apply]
  -- ⊢ ∑' (i : F × (Fin ϑ → F)), (pure i) (x, y) = 1
  rw [tsum_eq_single ((x, y) : α × β)]
  · -- ⊢ (if (x, y) = (x, y) then 1 else 0) = 1
    simp only [ite_true]
  · -- Goal 2: Prove all other terms are 0
    intro i h_ne
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
    exact id (Ne.symm h_ne)

/--
**Generic Probability Splitting Lemma (via Equivalence)**

This lemma proves that a single probability statement over a uniform
distribution on a type `α` can be rewritten as a sequential probability
statement over two smaller, independent distributions `γ` and `δ`,
given an equivalence `e : α ≃ γ × δ`.

This is a formal "change of variables" for probabilities, and it's
the generic version of `prob_split_randomness_apply`.
It allows us to "split" one `let` into two.
-/
theorem prob_split_uniform_sampling_of_equiv_prod {α γ δ : Type}
    -- Fintype & Nonempty assumptions for all types
    [Fintype α] [Fintype γ] [Fintype δ]
    [Nonempty α] [Nonempty γ] [Nonempty δ]
    -- The equivalence that splits α into γ × δ
    (e : α ≃ γ × δ)
    -- The predicate on the original (combined) type
    (P : α → Prop)
    -- Decidability for the predicates
    [DecidablePred P]
    [DecidablePred (fun xy : γ × δ => P (e.symm xy))] :

    -- LHS: Probability over the combined space
    Pr_{ let r ← $ᵖ α }[ P r ] =

    -- RHS: Probability over the sequential, split spaces
    Pr_{ let x ← $ᵖ γ; let y ← $ᵖ δ }[ P (e.symm (x, y)) ] := by

  -- 1. Unroll the LHS (a single `let`) using `prStx_unfold_final`
  -- LHS = ∑' r, Pr[r] * (if P r then 1 else 0)
  rw [prob_tsum_form_singleton]
  let D_rest := fun (x : γ) => (do
    let y ← $ᵖ δ
    return (P (e.symm (x, y)))
  )
  conv_rhs =>
    apply prob_tsum_form_split_first (D := $ᵖ γ) (D_rest := D_rest)
  simp_rw [D_rest]

  simp only [PMF.uniformOfFintype_apply, mul_ite, mul_one, mul_zero]
  simp_rw [prob_tsum_form_singleton]
  -- ⊢ (∑' (x : α), ... = ∑' (x : γ), (↑(Fintype.card γ))⁻¹ * ∑' (x_1 : δ), ...
  conv_rhs => enter [1, x]; rw [←ENNReal.tsum_mul_left]
  -- ⊢ (∑' (x : α), ... = ∑' (x : γ) (i : δ), ...
  rw [←ENNReal.tsum_prod]
  -- ⊢ (∑' (x : α), ...) = (∑' (p : γ × δ), ...)
  conv_lhs =>
    rw [tsum_eq_sum (α := ENNReal) (β := α) (f :=
      fun x => if P x then (↑(Fintype.card α))⁻¹ else 0) (s := Finset.univ) (hf := fun b => by
      simp only [mem_univ, not_true_eq_false, ite_eq_right_iff, ENNReal.inv_eq_zero,
        IsEmpty.forall_iff]
    )]
  conv_rhs =>
    rw [tsum_eq_sum (α := ENNReal) (β := γ × δ) (f := fun x =>
      (↑(Fintype.card γ))⁻¹ * (($ᵖ δ) x.2 * if P (e.symm x) then 1 else 0)
    ) (s := Finset.univ) (hf := fun b => by
      simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
    )]
  -- ⊢ (∑ b : α, .. = ..) = (∑ b : γ × δ, ..)
  have hcard_of_equiv: (Fintype.card α) = (Fintype.card (γ × δ)) := Fintype.card_congr e

  rw [Finset.sum_equiv (s := Finset.univ (α := α)) (t := Finset.univ (α := γ × δ))
    (f := fun x => if P x then (↑(Fintype.card α))⁻¹ else 0)
    (g := fun x => (↑(Fintype.card γ))⁻¹ * (($ᵖ δ) x.2 * if P (e.symm x) then 1 else 0))
    (e := e) (hst := fun i => by
    simp only [mem_univ]
  ) (hfg := fun i => by
    simp only [mem_univ, PMF.uniformOfFintype_apply, Equiv.symm_apply_apply, mul_ite, mul_one,
      mul_zero, forall_const]
    by_cases hP : P i
    · simp only [hP, ↓reduceIte]
      rw [hcard_of_equiv]
      rw [ENNReal.mul_inv_rev_ENNReal (ha := Fintype.card_ne_zero) (hb := Fintype.card_ne_zero)]
      rw [Fintype.card_prod]; rw [Nat.cast_mul]
    · simp only [hP, ↓reduceIte]
  )]
/-- Rewrites the probability over the large `r` space as a sequential
probability, sampling `r_last` *first*, then `r_init`.
-/
theorem prob_split_last_uniform_sampling_of_finFun {ϑ : ℕ} {F : Type} [Fintype F] [Nonempty F]
    (P : F → (Fin ϑ → F) → Prop)
    [DecidablePred (fun r : Fin (ϑ + 1) → F => P (r (Fin.last ϑ)) (fun i => r i.castSucc))]
    [∀ r_last, DecidablePred (fun r_init => P r_last r_init)] :
    Pr_{ let r ← $ᵖ (Fin (ϑ + 1) → F) }[ P (r (Fin.last ϑ)) (fun i ↦ r i.castSucc) ] =
    Pr_{ let r_last ← $ᵖ F; let r_init ← $ᵖ (Fin ϑ → F) }[ P r_last r_init ] := by
  rw [prob_tsum_form_doubleton]

  let e : (Fin (ϑ + 1) → F) ≃ F × (Fin ϑ → F) := equivFinFunSplitLast
  conv_lhs =>
    rw [prob_split_uniform_sampling_of_equiv_prod (e := e)]
  rw [prob_tsum_form_doubleton]
  congr 1
  funext xy
  congr 1
  have hEquiv_r_last : e.symm (xy.1, xy.2) (Fin.last ϑ) = xy.1 := by
    simp only [equivFinFunSplitLast, Prod.mk.eta, Equiv.coe_fn_symm_mk, Fin.snoc_last, e]
  have hEquiv_r_init : ∀ i: Fin ϑ, e.symm (xy.1, xy.2) i.castSucc = xy.2 i := by
    simp only [equivFinFunSplitLast, Prod.mk.eta, Equiv.coe_fn_symm_mk, Fin.snoc_castSucc,
      implies_true, e]
  simp_rw [hEquiv_r_last, hEquiv_r_init]

/--
Helper lemma for probability marginalization.
`Pr_{ (x, y) ← D₁ × D₂ }[ P x ] = Pr_{ x ← D₁ }[ P x ]`
-/
theorem prob_marginalization_first_of_prod {α β : Type} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (P : α → Prop) [DecidablePred P] :
  Pr_{let r ← $ᵖ (α × β) }[ P r.1 ] = Pr_{ let x ← $ᵖ α }[ P x ] := by
  rw [prob_split_uniform_sampling_of_prod]

  let D_rest := fun (x : α) => (do
    let y ← $ᵖ β
    pure (P (x, y).1)
  )
  conv_lhs =>
    apply prob_tsum_form_split_first (D := $ᵖ α) (D_rest := D_rest)
  simp_rw [prob_tsum_form_singleton]
  congr 1
  funext x
  congr 1
  unfold D_rest
  -- ⊢ (D_rest x) True = if P x then 1 else 0
  simp only [Bind.bind, pure, PMF.bind_const, PMF.pure_apply, eq_iff_iff, true_iff]
/--
**Monotonicity of Probability**

If event `A` (defined by predicate `f`) implies event `B` (defined by
predicate `g`) for all outcomes `r`, then the probability of `A`
is less than or equal to the probability of `B`.
-/
theorem Pr_le_Pr_of_implies {α : Type} (D : PMF α)
    (f g : α → Prop) [DecidablePred f] [DecidablePred g]
    (h_imp : ∀ r, f r → g r) :
    Pr_{ let r ← D }[ f r ] ≤ Pr_{ let r ← D }[ g r ] := by
  -- 1. Unroll both probability statements into their sum forms
  rw [prob_tsum_form_singleton D f]
  rw [prob_tsum_form_singleton D g]
  -- Goal: ⊢ (∑' r, D r * if f r then 1 else 0) ≤ (∑' r, D r * if g r then 1 else 0)
  -- 2. Apply tsum_le_tsum: We need to show term-wise inequality
  apply ENNReal.tsum_le_tsum
  -- 3. Show the term-wise inequality for each r
  intro r
  -- Goal: ⊢ D r * (if f r then 1 else 0) ≤ D r * (if g r then 1 else 0)
  -- Use `mul_le_mul_left'` which requires proving D r ≠ 0 and D r ≠ ∞
  -- Or simpler: use `mul_le_mul_of_nonneg_left` which only requires D r ≥ 0
  apply mul_le_mul_of_nonneg_left
  -- 4. Prove the inequality between the `ite` terms using the implication
  · by_cases hf : f r
    · simp only [hf, ↓reduceIte, h_imp, le_refl]
    · simp only [hf, ↓reduceIte, zero_le]
  -- 5. Prove the factor `D r` is non-negative
  · exact zero_le (D r) -- Probabilities are always non-negative

theorem Pr_multi_let_equiv_single_let {α β : Type}
    (D₁ : PMF α) (D₂ : PMF β) -- Assuming D₂ is independent for simplicity
    (P : α → β → Prop) [∀ x, DecidablePred (P x)] :
    -- LHS: Multi-let probability
    Pr_{ let x ← D₁; let y ← D₂ }[ P x y ]
    =
    -- RHS: Single-let probability over the combined distribution
    let D_combined : PMF (α × β) := do { let x ← D₁; let y ← D₂; pure (x, y) }
    Pr_{ let r ← D_combined }[ P r.1 r.2 ] := by
  dsimp only [Lean.Elab.WF.paramLet] -- Expose LHS do block
  simp only [bind_pure_comp, _root_.map_bind, Functor.map_map]

/--
**Law of Total Probability (Partitioning an Event)**
The probability of an event `f r` occurring can be calculated by
summing the probabilities of two disjoint cases:
1. `f r` occurs AND `g r` occurs.
2. `f r` occurs AND `g r` does NOT occur.
Good to be used with `Pr_multi_let_equiv_single_let`
-/
theorem Pr_add_split_by_complement {α : Type} (D : PMF α)
    (f g : α → Prop) [DecidablePred f] [DecidablePred g]
    -- Need decidability for the combined predicates too
    [DecidablePred (fun r => g r ∧ f r)]
    [DecidablePred (fun r => ¬(g r) ∧ f r)] :
    Pr_{ let r ← D }[ f r ] =
    (D >>= (fun r => pure (g r ∧ f r))) True + Pr_{ let r ← D }[ ¬(g r) ∧ f r ] := by
  -- 1. Unroll all three probability statements into their tsum forms
  rw [prob_tsum_form_singleton D f]
  rw [prob_tsum_form_singleton D (fun r => g r ∧ f r)]
  rw [prob_tsum_form_singleton D (fun r => ¬(g r) ∧ f r)]
  -- 2. Combine the two sums on the RHS using ENNReal.tsum_add
  -- Need to prove summability for both, which is true in ENNReal
  rw [← ENNReal.tsum_add]
  congr 1
  funext r
  rw [←mul_add]
  congr 1
  by_cases hg : g r
  · simp only [hg, true_and, not_true_eq_false, false_and, ↓reduceIte, add_zero]
  · simp only [hg, false_and, ↓reduceIte, not_false_eq_true, true_and, zero_add]

example : -- Pr_split_two_complements
  let f := fun (x, _) => x = true
  let g := fun (_, y) => y = true
  Pr_{ let x ← $ᵖ Bool; let y ← $ᵖ Bool }[ f (x, y) ] =
  Pr_{ let x ← $ᵖ Bool; let y ← $ᵖ Bool }[ g (x, y) ∧ f (x, y) ] +
  Pr_{ let x ← $ᵖ Bool; let y ← $ᵖ Bool }[ ¬(g (x, y)) ∧ f (x, y) ] := by
    let D : PMF (Bool × Bool) := do
      let x ← $ᵖ Bool
      let y ← $ᵖ Bool
      pure (x, y)
    set f := fun ((x, y) : (Bool × Bool)) => x = true
    set g := fun ((x, y) : (Bool × Bool)) => y = true
    simp only
    rw [Pr_multi_let_equiv_single_let (D₁ := $ᵖ Bool) (D₂ := $ᵖ Bool)]
    rw [Pr_multi_let_equiv_single_let (D₁ := $ᵖ Bool) (D₂ := $ᵖ Bool)]
    rw [Pr_multi_let_equiv_single_let (D₁ := $ᵖ Bool) (D₂ := $ᵖ Bool)]
    rw [Pr_add_split_by_complement (D := D) (f := f) (g := g)]

/--
`Pr_{r ← D}[ P_out ∧ P(r) ] = (if P_out then Pr_{r ← D}[ P(r) ] else 0)`
-/
theorem prob_const_and_prop_eq_ite {α : Type} (D : PMF α)
    (P_out : Prop) [Decidable P_out]
    (P : α → Prop) [DecidablePred P] :
    Pr_{ let r ← D }[ P_out ∧ P r ] = if P_out then Pr_{ let r ← D }[ P r ] else 0 := by
  by_cases h_P_out : P_out
  · -- Case 1: P_out is True
    simp only [h_P_out, if_true, true_and]
  · -- Case 2: P_out is False
    simp only [h_P_out, if_false, false_and]
    rw [prob_tsum_form_singleton]
    simp only [if_false, mul_zero, tsum_zero]
end ProbabilityTools

universe u v w k l
variable {κ : Type k} {ι : Type l} [Fintype ι] [Nonempty ι] -- κ => row indices, ι => column indices
variable {F : Type v} [Semiring F] [Fintype F]
-- variable {M : Type} [Fintype M] -- Message space type
variable {A : Type w} [Fintype A] [DecidableEq A] [AddCommMonoid A] [Module F A] -- Alphabet type

instance instDecidableEqWord : DecidableEq (κ → A) := Classical.typeDecidableEq (κ → A)
instance instDecidableEqInterleavedWordRow :
  ∀ _: ι, DecidableEq (κ → A) := fun _ ↦ instDecidableEqWord

section GenericCodeDefinitions

abbrev CodewordSpace (ι : Type u) (A : Type w) := Set (ι → A) -- CodewordSpace ι A

/-- Heterogeneous linear code: a linear code over a semiring F with alphabet A,
which is a module over F. -/
abbrev HLinearCode (ι : Type u) (F : Type v) [Semiring F] -- HLinearCode ι F A
    (A : Type w) [AddCommMonoid A] [Module F A] : Type (max u w) :=
  letI : Module F (ι → A) := by apply Pi.module (I := ι) (f := fun _ => A)
  Submodule F (ι → A)

/-- Homogeneous linear code: a linear code over a semiring F with the same alphabet F. -/
abbrev HomLinearCode (ι : Type u) [Fintype ι] (F : Type v) [Semiring F] :=
  HLinearCode ι F F

lemma HomLinearCode_eq_LinearCode {ι : Type u} [Fintype ι] {F : Type v} [Semiring F] :
  HomLinearCode ι F = LinearCode ι F := by rfl

def transposeFinMap (V : ι → (κ → A)) : κ → (ι → A) :=
  fun j i => V i j

def getRow (U : ι → (κ → A)) (rowIdx : κ) : ι → A :=
  transposeFinMap U rowIdx

omit [Fintype ι] [Nonempty ι] [Fintype A] [DecidableEq A] [AddCommMonoid A] in
lemma getCellInterleavedWord_eq (u : ι → (κ → A)) (rowIdx : κ) (colIdx : ι) :
  u colIdx rowIdx = (getRow (u) rowIdx) colIdx:= by
  simp only [getRow, transposeFinMap]

omit [Fintype ι] [Nonempty ι] [Fintype A] [DecidableEq A] [AddCommMonoid A] in
lemma interleavedWord_eq_iff_allRowsEq (u v : ι → (κ → A)) :
  u = v ↔ ∀ rowIdx, getRow u rowIdx = getRow v rowIdx := by
  constructor
  · intro h rowIdx
    exact congrFun (congrArg getRow h) rowIdx
  · intro h
    ext c r
    rw [getCellInterleavedWord_eq u r c, getCellInterleavedWord_eq v r c]
    exact congrFun (h r) c

lemma Code.dist_eq_minDist {ι : Type l} [Fintype ι] -- Length Type
    {F : Type v} [DecidableEq F] -- Alphabet Type
    {C : Set (ι → F)} : -- Code
    Code.dist C = Code.minDist C := by
  -- 1. Define the sets
  let S_le : Set ℕ := {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v ≤ d}
  let S_eq : Set ℕ := {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d}
  -- Apply antisymmetry
  apply le_antisymm
  · -- 2. Prove dist C ≤ minDist C (i.e., sInf S_le ≤ sInf S_eq)
    -- This relies on finding an element achieving Nat.sInf S_eq
    by_cases hS_eq_nonempty : S_eq.Nonempty
    · -- Case: S_eq is non-empty
      -- Get the minimum element d_min which exists and equals sInf S_eq
      obtain ⟨d_min, hd_min_in_Seq, hd_min_is_min⟩ := Nat.sInf_mem hS_eq_nonempty
      -- hd_min_is_min : ∃ v ∈ C, d_min ≠ v ∧ Δ₀(d_min, v) = sInf S_eq
      rcases hd_min_is_min with ⟨v, hv, hne, hdist_eq_dmin⟩
      dsimp only [S_eq] at hdist_eq_dmin
      dsimp only [Code.minDist, ne_eq]
      rw [←hdist_eq_dmin] -- Replace sInf S_eq with d_min
      -- Show d_min is in S_le
      have hd_min_in_Sle : Δ₀(d_min, v) ∈ S_le := by
        use d_min, hd_min_in_Seq, v, hv, hne
      -- Since d_min is in S_le, sInf S_le must be less than or equal to it
      apply Nat.sInf_le hd_min_in_Sle
    · -- Case: S_eq is empty
      simp only [Set.not_nonempty_iff_eq_empty, S_eq] at hS_eq_nonempty
      simp only [dist, ne_eq, Code.minDist, hS_eq_nonempty]
      rw [Nat.sInf_empty]
      have hS_le_empty : S_le = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro d hd_in_Sle
        rcases hd_in_Sle with ⟨u, hu, v, hv, hne, hdist_le_d⟩
        -- If such u,v,hne existed, then d' = hammingDist u v would be in S_eq.
        have hd'_in_Seq : hammingDist u v ∈ S_eq := ⟨u, hu, v, hv, hne, rfl⟩
        simp_rw [S_eq, hS_eq_nonempty] at hd'_in_Seq
        exact hd'_in_Seq -- mem ∅
      -- sInf of empty set is 0.
      simp_rw [S_le] at hS_le_empty
      rw [hS_le_empty, Nat.sInf_empty]
  · -- 3. Prove minDist C ≤ dist C (i.e., sInf S_eq ≤ sInf S_le)
    -- Show sInf S_le is a lower bound for S_eq
    by_cases hS_le_nonempty : S_le.Nonempty
    · -- Case: S_le is non-empty
      obtain ⟨d_min, hd_min_in_Seq, hd_min_is_min⟩ := Nat.sInf_mem hS_le_nonempty
      -- hd_min_is_min : ∃ v ∈ C, d_min ≠ v ∧ Δ₀(d_min, v) = sInf S_le
      rcases hd_min_is_min with ⟨v, hv, hne, hdist_le_dmin⟩
      dsimp only [S_le] at hdist_le_dmin
      dsimp only [dist]
      have h :  minDist C ≤ Δ₀(d_min, v) := by
        apply Nat.sInf_le
        use d_min, hd_min_in_Seq, v, hv, hne
      omega
    · -- Case: S_le is empty
      -- If S_le is empty, sInf S_le = 0
      -- ⊢ minDist C ≤ ‖C‖₀
      simp only [Set.nonempty_iff_ne_empty, ne_eq, not_not, S_le] at hS_le_nonempty
      rw [dist, hS_le_nonempty, Nat.sInf_empty]
      -- Goal: ⊢ minDist C ≤ 0
      -- Since minDist C is a Nat, this implies minDist C = 0
      rw [Nat.le_zero]
      -- Goal: ⊢ minDist C = 0
      rw [minDist]
      -- Goal: ⊢ sInf S_eq = 0
      have hS_eq_empty : S_eq = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr -- Prove by showing no element d is in S_eq
        intro d hd_in_Seq -- Assume d ∈ S_eq
        -- Unpack the definition of S_eq
        rcases hd_in_Seq with ⟨u, hu, v, hv, hne, hdist_eq_d⟩
        -- If such u, v, hne exist, then d = Δ₀(u, v) must be in S_le
        -- because Δ₀(u, v) ≤ d (as they are equal)
        have hd_in_Sle : d ∈ S_le := by
          use u, hu, v, hv, hne
          exact le_of_eq hdist_eq_d -- Use d' ≤ d where d' = Δ₀(u, v) = d
        -- But we know S_le is empty, so d cannot be in S_le
        simp_rw [S_le, hS_le_nonempty] at hd_in_Sle -- Rewrites the goal to `d ∈ ∅`
        exact hd_in_Sle -- This provides the contradiction (proof of False)
      simp_rw [S_eq] at hS_eq_empty
      rw [hS_eq_empty, Nat.sInf_empty]

omit [Nonempty ι] [Fintype A] [AddCommMonoid A] in
lemma exists_closest_codeword (u : ι → A) (C : Set (ι → A)) [Nonempty C] :
    ∃ M ∈ C, Δ₀(u, M) = Δ₀(u, C) := by
  -- Set up similar to uniqueClosestCodeword
  set S := (fun (x : C) => Δ₀(u, x)) '' Set.univ
  have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
  -- Use the fact that we can find a minimum element in S
  let SENat := (fun (g : C) => (Δ₀(u, g) : ENat)) '' Set.univ
    -- let S_nat := (fun (g : C_i) => hammingDist f g) '' Set.univ
  have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
  have h_coe_sinfS_eq_sinfSENat : ↑(sInf S) = sInf SENat := by
    rw [ENat.coe_sInf (hs := hS_nonempty)]
    simp only [SENat, Set.image_univ, sInf_range]
    simp only [S, Set.image_univ, iInf_range]
  rcases Nat.sInf_mem hS_nonempty with ⟨g_subtype, hg_subtype, hg_min⟩
  rcases g_subtype with ⟨M_closest, hg_mem⟩
  -- The distance `d` is exactly the Hamming distance of `U` to `M_closest` (lifted to `ℕ∞`).
  have h_dist_eq_hamming : Δ₀(u, C) = (hammingDist u M_closest) := by
    -- We found `M_closest` by taking the `sInf` of all distances, and `hg_min`
    -- shows that the distance to `M_closest` achieves this `sInf`.
    have h_distFromCode_eq_sInf : Δ₀(u, C) = sInf SENat := by
      apply le_antisymm
      · -- Part 1 : `d ≤ sInf ...`
        simp only [distFromCode]
        apply sInf_le_sInf
        intro a ha
        -- `a` is in `SENat`, so `a = ↑Δ₀(f, g)` for some codeword `g`.
        rcases (Set.mem_image _ _ _).mp ha with ⟨g, _, rfl⟩
        -- We must show `a` is in the set for `d`, which is `{d' | ∃ v, ↑Δ₀(f, v) ≤ d'}`.
        -- We can use `g` itself as the witness `v`, since `↑Δ₀(f, g) ≤ ↑Δ₀(f, g)`.
        use g; simp only [Subtype.coe_prop, le_refl, and_self]
      · -- Part 2 : `sInf ... ≤ d`
        simp only [distFromCode]
        apply le_sInf
        -- Let `d'` be any element in the set that `d` is the infimum of.
        intro d' h_d'
        -- Unpack `h_d'` : there exists some `v` in the code such that
        -- `↑(hammingDist f v) ≤ d'`.
        rcases h_d' with ⟨v, hv_mem, h_dist_v_le_d'⟩
        -- By definition, `sInf SENat` is a lower bound for all elements in `SENat`.
        -- The element `↑(hammingDist f v)` is in `SENat`.
        have h_sInf_le_dist_v : sInf SENat ≤ ↑(hammingDist u v) := by
          apply sInf_le -- ⊢ ↑Δ₀(f, v) ∈ SENat
          rw [Set.mem_image]
          -- ⊢ ∃ x ∈ Set.univ, ↑Δ₀(f, ↑x) = ↑Δ₀(f, v)
          simp only [Set.mem_univ, Nat.cast_inj, true_and, Subtype.exists, exists_prop]
          -- ⊢ ∃ a ∈ C_i, Δ₀(f, a) = Δ₀(f, v)
          use v -- exact And.symm ⟨rfl, hv_mem⟩
        -- Now, chain the inequalities : `sInf SENat ≤ ↑(dist_to_any_v) ≤ d'`.
        exact h_sInf_le_dist_v.trans h_dist_v_le_d'
    rw [h_distFromCode_eq_sInf, ←h_coe_sinfS_eq_sinfSENat, ←hg_min]
  use M_closest, hg_mem, h_dist_eq_hamming.symm

lemma Code.closeToCode_iff_closeToCodeword {ι : Type u} [Fintype ι] {F : Type v} [DecidableEq F]
    {C : Set (ι → F)} [Nonempty C] (u : ι → F) (e : ℕ) :
  Δ₀(u, C) ≤ e ↔ ∃ v ∈ C, Δ₀(u, v) ≤ e := by
  constructor
  · -- Direction 1: (→)
    -- Assume: Δ₀(u, C) ≤ ↑e
    -- Goal: ∃ v ∈ C, Δ₀(u, v) ≤ e
    intro h_dist_le_e
    -- We need to handle two cases: the code C being empty or non-empty.
    by_cases hC_empty : C = ∅
    · -- Case 1: C is empty
      -- The goal is `∃ v ∈ ∅, ...`, which is `False`.
      -- We must show the assumption `h_dist_le_e` is also `False`.
      rw [hC_empty] at h_dist_le_e
      rw [distFromCode_of_empty] at h_dist_le_e
      -- h_dist_le_e is now `⊤ ≤ ↑e`.
      -- Since `e : ℕ`, `↑e` is finite (i.e., `↑e ≠ ⊤`).
      have h_e_ne_top : (e : ℕ∞) ≠ ⊤ := ENat.coe_ne_top e
      -- `⊤ ≤ ↑e` is only true if `↑e = ⊤`, so this is a contradiction.
      simp only [top_le_iff, ENat.coe_ne_top] at h_dist_le_e
    · -- Case 2: C is non-empty
      -- We can now use `exists_closest_codeword`
      have hC_nonempty : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_empty
      have h_exists_closest : ∃ M ∈ C, Δ₀(u, C) = ↑(Δ₀(u, M)) := by
        let res := exists_closest_codeword u C
        rcases res with ⟨M, hM_mem, hM_dist_eq⟩
        use M, hM_mem
        exact id (Eq.symm hM_dist_eq)
      -- Now we use this fact.
      rcases h_exists_closest with ⟨M, hM_mem, hM_dist_eq⟩
      -- Substitute this into our assumption `h_dist_le_e`
      rw [hM_dist_eq] at h_dist_le_e
      -- h_dist_le_e is now: `↑(Δ₀(u, M)) ≤ ↑e`
      -- We can cancel the `↑` (coercion) from both sides
      rw [ENat.coe_le_coe] at h_dist_le_e
      -- h_dist_le_e is now: `Δ₀(u, M) ≤ e` (as `ℕ`)
      -- This is exactly what we need to prove!
      use M, hM_mem
  · -- Direction 2: (←)
    -- Assume: `∃ v ∈ C, Δ₀(u, v) ≤ e`
    -- Goal: `Δ₀(u, C) ≤ ↑e`
    intro h_exists
    -- Unpack the assumption
    rcases h_exists with ⟨v, hv_mem, h_dist_le_e⟩
    -- Goal is `sInf {d | ∃ w ∈ C, ↑(Δ₀(u, w)) ≤ d} ≤ ↑e`
    -- We can use the lemma `ENat.sInf_le` (or `sInf_le` for complete linear orders)
    -- which says `sInf S ≤ x` if `x ∈ S`.
    have h_sInf_le: Δ₀(u, C) ≤ Δ₀(u, v) := by
      apply sInf_le
      simp only [Set.mem_setOf_eq, Nat.cast_le]
      use v
    calc Δ₀(u, C) ≤ Δ₀(u, v) := h_sInf_le
    _ ≤ e := by exact ENat.coe_le_coe.mpr h_dist_le_e

omit [Nonempty ι] [Fintype A] [AddCommMonoid A] in
theorem closeToWord_iff_exists_possibleDisagreeCols
    (u : ι → A) (v : ι → A) (e : ℕ) :
    Δ₀(u, v) ≤ e ↔ ∃ (D : Finset ι),
      D.card ≤ e ∧ (∀ (colIdx : ι), colIdx ∉ D → u colIdx = v colIdx) := by
  constructor
  · -- Direction 1: Δ₀(u, v) ≤ e → ∃ D, ...
    intro h_dist_le_e
    -- Define D as the set of disagreeing columns
    let D : Finset ι := Finset.filter (fun colIdx => u colIdx ≠ v colIdx) Finset.univ
    use D
    constructor
    · -- Prove D.card ≤ e
      have hD_card_eq_dist : D.card = hammingDist u v := by
        simp only [hammingDist, ne_eq, D]
      rw [hD_card_eq_dist]
      -- Assume Δ₀(word, codeword) = hammingDist word codeword (perhaps needs coercion)
      -- Let's assume Δ₀ returns ℕ∞ and hammingDist returns ℕ for now
      apply ENat.coe_le_coe.mp -- Convert goal to ℕ ≤ ℕ
      -- Goal: ↑(hammingDist u ↑v) ≤ ↑e
      rw [Nat.cast_le (α := ENat)]
      exact h_dist_le_e
    · -- Prove agreement outside D
      intro colIdx h_colIdx_notin_D
      -- h_colIdx_notin_D means colIdx is not in the filter
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        ne_eq, not_not, D] at h_colIdx_notin_D
      -- Therefore, u colIdx = v.val colIdx
      exact h_colIdx_notin_D
  · -- Direction 2: (∃ D, ...) → Δ₀(u, v) ≤ e
    intro h_exists_D
    rcases h_exists_D with ⟨D, hD_card_le_e, h_agree_outside_D⟩
    -- Goal: Δ₀(u, v) ≤ e

    -- Consider the set where u and v differ
    let Diff_set := Finset.filter (fun colIdx => u colIdx ≠ v colIdx) Finset.univ
    -- Show that Diff_set is a subset of D
    have h_subset : Diff_set ⊆ D := by
      intro colIdx h_diff -- Assume colIdx is in Diff_set, i.e., u colIdx ≠ v.val colIdx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Diff_set] at h_diff
      -- We need to show colIdx ∈ D
      -- Suppose colIdx ∉ D for contradiction
      by_contra h_notin_D
      -- Then by h_agree_outside_D, u colIdx = v.val colIdx
      have h_eq := h_agree_outside_D colIdx h_notin_D
      -- This contradicts h_diff
      exact h_diff h_eq

    -- Use card_le_card and the properties
    have h_card_diff_le_card_D : Diff_set.card ≤ D.card := Finset.card_le_card h_subset
    have h_dist_eq_card_diff : hammingDist u v = Diff_set.card := by
      simp only [hammingDist, ne_eq, Diff_set]

    -- Combine the inequalities
    -- Assuming Δ₀(w, c) = ↑(hammingDist w c)
    rw [← ENat.coe_le_coe] -- Convert goal to ℕ∞ ≤ ℕ∞
    -- Goal: ↑(hammingDist u ↑v) ≤ ↑e
    apply le_trans (ENat.coe_le_coe.mpr (by rw [h_dist_eq_card_diff]))
    apply ENat.coe_le_coe.mpr
    exact Nat.le_trans h_card_diff_le_card_D hD_card_le_e

omit [Nonempty ι] [Semiring F] [Fintype F] in
/--
A non-trivial code (a code with at least two distinct codewords)
must have a minimum distance greater than 0.
-/
lemma Code.dist_pos_of_Nontrivial {C : Set (ι → F)} [DecidableEq F]
    (hC : Set.Nontrivial C) : Code.dist C > 0 := by
  -- 1. Use the equivalence we just proved
  rw [Code.dist_eq_minDist]
  unfold Code.minDist
  let S_eq : Set ℕ := {d | ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ hammingDist u v = d}
  -- 2. `hC : Set.Nontrivial C` means `∃ u ∈ C, ∃ v ∈ C, u ≠ v`
  rcases hC with ⟨u, hu, v, hv, hne⟩
  -- 3. This implies S_eq is non-empty, because the distance d' = Δ₀(u, v) is in it
  let d' := hammingDist u v
  have hd'_in_Seq : d' ∈ S_eq := ⟨u, hu, v, hv, hne, rfl⟩
  have hS_eq_nonempty : S_eq.Nonempty := ⟨d', hd'_in_Seq⟩
  -- 4. Get the minimum element d_min = sInf S_eq
  let d_min := sInf S_eq
  -- 5. By `Nat.sInf_mem_of_nonempty`, this minimum d_min is itself an element of S_eq
  have h_d_min_in_Seq : d_min ∈ S_eq := by
    exact Nat.sInf_mem hS_eq_nonempty
  -- 6. Unpack the proof that d_min ∈ S_eq
  --    This gives us a pair (u', v') that *achieves* this minimum distance
  rcases h_d_min_in_Seq with ⟨u', hu', v', hv', hne', hdist_eq_dmin⟩
  -- 7. The goal is to show d_min > 0.
  -- We know d_min = hammingDist u' v' from hdist_eq_dmin
  dsimp only [d_min, S_eq] at hdist_eq_dmin
  rw [←hdist_eq_dmin]
  exact hammingDist_pos.mpr hne'

omit [Fintype ι] [Nonempty ι] in
theorem ReedSolomonCode.dist {n k : ℕ} {F : Type*} [NeZero n] [NeZero k] (h : k ≤ n)
    {domain : (Fin n) ↪ F} [DecidableEq F] [Field F] [Fintype ι] :
    Code.dist (R := F) ((ReedSolomon.code domain k) : Set (Fin n → F)) = n - k + 1 := by
  have hMinDist := ReedSolomonCode.minDist (F := F) (n := k) (m := n)
    (α := domain.toFun) (inj := domain.inj') (h := h)
  rw [←Code.dist_eq_minDist] at hMinDist
  exact hMinDist

def pickClosestCodeword (u : ι → A) (C : HLinearCode ι F A) : C := by
  have h_exists := exists_closest_codeword u C
  let M_val := Classical.choose h_exists
  have h_M_spec := Classical.choose_spec h_exists
  exact ⟨M_val, h_M_spec.1⟩

omit [Nonempty ι] [Fintype F] [Fintype A] in
lemma distFromPickClosestCodeword (u : ι → A) (C : HLinearCode ι F A) :
    Δ₀(u, C) = Δ₀(u, pickClosestCodeword u C) := by
  have h_exists := exists_closest_codeword u C
  have h_M_spec := Classical.choose_spec h_exists
  -- reapply the choose spec for definitional equality
  exact h_M_spec.2.symm

variable (HLC : HLinearCode ι F A)

/-- Interleaved code submodule of any HLinearCode, we name it `HLinearInterleavedCode` -/
instance HLinearCode.interleavedCodeSubmodule : Submodule F (ι → (κ → A)) := {
  carrier := { V : ι → (κ → A) | ∀ i, transposeFinMap V i ∈ HLC }
  add_mem' hU hV i := HLC.add_mem (hU i) (hV i)
  zero_mem' _ := HLC.zero_mem
  smul_mem' a _ hV i := HLC.smul_mem a (hV i)
}

/-- Interleaved code of any HLinearCode, where κ is the row index set
`HLinearCode -> HLinearInterleavedCode` -/
instance HLinearCode.toInterleavedCode (κ : Type k) (HLC : HLinearCode ι F A)
  : HLinearCode ι F (κ → A) := HLinearCode.interleavedCodeSubmodule HLC

omit [Fintype ι] [Nonempty ι] [Fintype F] [Fintype A] [DecidableEq A] in
lemma mem_HLinearInterleavedCode (U : ι → (κ → A)) (HLC : HLinearCode ι F A) :
  U ∈ HLC.toInterleavedCode κ ↔ ∀ i, getRow U i ∈ HLC := by
    rfl

omit [Fintype ι] [Nonempty ι] [Fintype F] [Fintype A] [DecidableEq A] in
def getRowOfInterleavedCodeword (U : ι → (κ → A)) (rowIdx : κ)
    (hU : U ∈ HLC.toInterleavedCode κ) : HLC :=
  ⟨getRow U rowIdx, by
    simp only [mem_HLinearInterleavedCode] at hU
    simp only [hU]
  ⟩

def HLinearCode.toCodewordSpace : CodewordSpace ι A := HLC

def HLinearInterleavedCode.getRowCodeword (U : HLC.toInterleavedCode (κ := κ))
    (rowIdx : κ) : HLC := by
  exact ⟨transposeFinMap (V := U.val) rowIdx, by
    have hU := U.property
    rw [mem_HLinearInterleavedCode] at hU
    exact hU rowIdx
  ⟩

/-- `e ∈ {0, …, ⌊(‖C‖₀ - 1) / 2⌋}`. This definition is compatible with
`Code.distFromCode_eq_of_lt_half_dist` -/
def HLinearCode.uniqueDecodingRadius : ℕ :=
  (‖(HLC : Set (ι → A))‖₀ - 1) / 2 + 1 -- + 1 as right bound buffer for usage of `Finset.range`

#eval
  let d := 5
  [d/2, (d - 1)/2 + 1]
#eval
  let d := 6
  [d/2, (d - 1)/2 + 1]

omit [Nonempty ι] [Fintype F] [Fintype A] in
/--
Given an error parameter `e` within the unique decoding radius of a
**non-trivial** code `HLC` (i.e., distance `d ≥ 1`), this lemma
proves the standard bound `2 * e < d`.
-/
lemma two_mul_unique_radius_dist_lt_d
    (HLC : HLinearCode ι F A)
    -- This hypothesis is crucial. It asserts the code is non-trivial.
    (h_dist_pos : ‖(HLC : Set (ι → A))‖₀ > 0)
    {e : ℕ}
    (he : e < HLinearCode.uniqueDecodingRadius HLC) :
    2 * e < ‖(HLC : Set (ι → A))‖₀ := by
  unfold HLinearCode.uniqueDecodingRadius at he
  -- 2. Simplify hypothesis `e < (d - 1) / 2 + 1` to `e ≤ (d - 1) / 2`
  --    In Nat, `x < y + 1` is equivalent to `x ≤ y`.
  rw [Nat.lt_succ_iff] at he
  -- he: e ≤ (‖(HLC : Set (ι → A))‖₀ - 1) / 2
  -- 3. Multiply by 2 (this is sound)
  have h_2e_le := Nat.mul_le_mul_left 2 he
  -- h_2e_le: 2 * e ≤ 2 * ((‖(HLC : Set (ι → A))‖₀ - 1) / 2)
  -- 4. This is the step I messed up.
  --    We prove `2 * (n / 2) ≤ n` using `Nat.mul_comm` and `Nat.div_mul_le_self`
  have h_div_prop : 2 * ((‖(HLC : Set (ι → A))‖₀ - 1) / 2) ≤ ‖(HLC : Set (ι → A))‖₀ - 1 := by
    rw [Nat.mul_comm]
    -- This is the correct lemma: (n / 2) * 2 ≤ n
    exact Nat.div_mul_le_self (‖(HLC : Set (ι → A))‖₀ - 1) 2
  -- 5. Chain the inequalities
  --    2 * e ≤ 2 * ((d - 1) / 2) ≤ d - 1
  have h_2e_le_d_minus_1 : 2 * e ≤ ‖(HLC : Set (ι → A))‖₀ - 1 :=
    le_trans h_2e_le h_div_prop
  -- 6. Convert `x ≤ y - 1` to `x < y`
  --    This uses `Nat.le_sub_one_iff_lt`, which requires the side goal `0 < y`
  rw [Nat.le_sub_one_iff_lt] at h_2e_le_d_minus_1
  -- 7. This is the goal
  · exact h_2e_le_d_minus_1
  -- 8. Prove the side goal `0 < ‖(HLC : Set (ι → A))‖₀`
  · exact h_dist_pos

/--
A generic code over an alphabet A with message space M and block length n
is an injective map Enc : M → (Fin n → A).
This aligns with the structure `C: M → (ι → A)` where M = `Σ^k`.
-/
structure ErrorCorrectingCode.{t} (M : Type t) (A : Type w) where
  codewordSpace : CodewordSpace ι A
  encode : M → codewordSpace
  injective : Function.Injective encode
  dist : codewordSpace → codewordSpace → ℕ∞

/-- Evaluation of an affine line across u₀ and u₁ at a point r -/
def affineLineEvaluation {F : Type v} [Ring F] [Module F A]
    (u₀ u₁ : ι → A) (r : F) : ι → A := (1 - r) • u₀ + r • u₁

/-- Interleave two codewords u₀ and u₁ into a single interleaved codeword -/
def interleaveWords (u : κ → (ι → A)) : ι → (κ → A) :=
  fun colIdx => fun rowIdx => u rowIdx colIdx

def finMapTwoWords (u₀ u₁ : ι → A) : (Fin 2 → ι → A) := fun rowIdx =>
  match rowIdx with
  | ⟨0, _⟩ => u₀
  | ⟨1, _⟩ => u₁

/-- Interleave two codewords u₀ and u₁ into a single interleaved codeword -/
def interleaveTwoWords (u₀ u₁ : ι → A) : ι → (Fin 2 → A) :=
  interleaveWords (κ := Fin 2) (ι := ι) (finMapTwoWords u₀ u₁)

omit [Fintype ι] [Nonempty ι] [Fintype F] [Fintype A] [DecidableEq A] in
theorem interleaveCodewords (u : κ → (ι → A)) (hu : ∀ rowIdx, u rowIdx ∈ HLC) :
  interleaveWords u ∈ HLC.toInterleavedCode κ := by
  simp only [HLinearCode.toInterleavedCode, HLinearCode.interleavedCodeSubmodule, Submodule.mem_mk,
    AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  intro i
  exact hu i

notation:20 "⊛|"u => interleaveWords u
notation:20 u "⊛₂" v => interleaveTwoWords u v

def HLinearCode.correlatedAgreement {HLC : HLinearCode ι F A} (u : κ → (ι → A)) (e : ℕ) : Prop :=
  Δ₀(⊛|u, HLC.toInterleavedCode κ) ≤ e

def HLinearCode.correlatedAgreement₂ {HLC : HLinearCode ι F A} (u₀ u₁ : ι → A) (e : ℕ) : Prop :=
  HLC.correlatedAgreement (finMapTwoWords u₀ u₁) e

def HLinearCode.interleavedWordCA (u v : κ → (ι → A)) (e : ℕ) : Prop :=
  Δ₀(⊛|u, ⊛|v) ≤ e

def HLinearCode.pairCorrelatedAgreement (u₀ u₁ v₀ v₁ : ι → A) (e : ℕ) : Prop :=
  Δ₀(u₀ ⊛₂ u₁, v₀ ⊛₂ v₁) ≤ e

omit [Nonempty ι] [Fintype F] [Fintype A] [DecidableEq A] in
theorem correlatedAgreement_iff_closeToInterleavedCodeword {HLC : HLinearCode ι F A}
    (u : κ → (ι → A)) (e : ℕ) :
    HLC.correlatedAgreement u e ↔ ∃ (v : HLC.toInterleavedCode κ), Δ₀(⊛|u, v) ≤ e := by
  unfold HLinearCode.correlatedAgreement
  have h := Code.closeToCode_iff_closeToCodeword (C := HLC.toInterleavedCode κ) (u := ⊛|u) (e := e)
  constructor
  · -- Direction 1: correlatedAgreement u e → ∃ v, Δ₀(⊛|u, v) ≤ e
    intro h_corr_agree -- Assume Δ₀(⊛|u, C^κ) ≤ e
    have res := h.mp h_corr_agree
    rcases res with ⟨v, hv_Mem, hv_dist_le_e⟩
    use ⟨v, hv_Mem⟩
  · -- Direction 2: (∃ v, Δ₀(⊛|u, v) ≤ e) → correlatedAgreement u e
    intro h_exists_v -- Assume ∃ v ∈ C^κ, Δ₀(⊛|u, v) ≤ e
    rcases h_exists_v with ⟨v, hvClose⟩
    have res := h.mpr (by
      use v;
      constructor
      · exact Subtype.coe_prop v
      · exact hvClose
    )
    exact res

----------------------------------------------------- Switch to (F : Type) for `Pr_{...}[...]` usage
variable {F : Type} [Ring F] [Module F A] [Fintype F] (HLC : HLinearCode ι F A)
/-
Definition 2.1. We say that `C ⊂ F^n` features proximity gaps for affine lines
with respect to the proximity parameter `e` and the false witness bound `ε` if, for
each pair of words `u_0` and `u_1` in `F^n`, if
`Pr_{r ∈ F}[d((1-r) · u_0 + r · u_1, C) ≤ e] > ε/q`
holds, then `d^2((u_i)_{i=0}^1, C^2) ≤ e` also does.
-/
structure ProximityGapAffineLines (e : ℕ) (ε : ℕ) where
  gap_property : ∀ u₀ u₁ : ι → A,
  (Pr_{ let r ←$ᵖ F }[ -- This syntax only works with (F : Type 0)
      (Δ₀(affineLineEvaluation (F := F) u₀ u₁ r, HLC) ≤ e: Prop)
    ] > ((ε: ℝ≥0) / (Fintype.card F : ℝ≥0))) →
      HLC.correlatedAgreement₂ u₀ u₁ e

omit [Nonempty ι] [Fintype A] [Fintype F] in
/-- **Lemma: Distance of Affine Combination is Bounded by Interleaved Distance** -/
theorem dist_affineCombination_le_dist_interleaved₂
    (u₀ u₁ v₀ v₁ : ι → A) (r : F) :
    Δ₀( affineLineEvaluation (F := F) u₀ u₁ r, affineLineEvaluation (F := F) v₀ v₁ r) ≤
      Δ₀(u₀ ⊛₂ u₁, v₀ ⊛₂ v₁) := by
  -- The goal is to prove card(filter L) ≤ card(filter R)
  -- We prove this by showing filter L ⊆ filter R
  apply Finset.card_le_card
  -- Use `monotone_filter_right` or prove subset directly
  intro j
  -- Assume j is in the filter set on the LHS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hj_row_diff
  -- Goal: Show j is in the filter set on the RHS
  unfold affineLineEvaluation at hj_row_diff
  -- hj_row_diff : ((1 - r) • u₀ + r • u₁) j ≠ ((1 - r) • v₀ + r • v₁) j
  -- ⊢ (u₀⊛₂u₁) j ≠ (v₀⊛₂v₁) j
  -- We prove this by contradiction
  by_contra h_cols_eq
  -- h_cols_eq : (u₀ ⊛₂ u₁) j = (v₀ ⊛₂ v₁) j
  -- `h_cols_eq` is a function equality. Apply it to row indices 0 and 1
  have h_row0_eq : (u₀ ⊛₂ u₁) j = (v₀ ⊛₂ v₁) j := by exact h_cols_eq
  simp only [Pi.add_apply, Pi.smul_apply, ne_eq] at hj_row_diff
  have h_row0_eq : (u₀ ⊛₂ u₁) j 0 = (v₀ ⊛₂ v₁) j 0 := congrFun h_cols_eq 0
  have h_row1_eq : (u₀ ⊛₂ u₁) j 1 = (v₀ ⊛₂ v₁) j 1 := congrFun h_cols_eq 1
  have h_row0 : u₀ j = v₀ j := by exact h_row0_eq
  have h_row1 : u₁ j = v₁ j := by exact h_row1_eq
  rw [h_row0, h_row1] at hj_row_diff
  exact hj_row_diff rfl -- since hj_row_diff has form : ¬(x = x)

end GenericCodeDefinitions

section TensorProximityGapDefinitions -- CommRing scalar set
variable {F : Type} [CommRing F] [Module F A] [Fintype F] (HLC : HLinearCode ι F A)

/-- The tensor product `⊗_{i=0}^{ϑ-1}(1 - rᵢ, rᵢ)` -/
def tensorProduct {ϑ : ℕ} (r : Fin ϑ → F) : Fin (2^ϑ) → F :=
  fun i ↦
    ∏ j : Fin ϑ, if Nat.getBit j i.val = 0 then ((1 : F) - r j ) else (r j)

--
def tensorCombine {ϑ : ℕ} (u : Fin (2 ^ ϑ) → (ι → A)) (r : Fin ϑ → F) : (ι → A) :=
  fun colIdx => ∑ u_rowIdx, (tensorProduct r u_rowIdx) • (u u_rowIdx colIdx)

set_option quotPrecheck false
notation:20 r"|⨂|"u => tensorCombine u r

def tensorCombine_affineLineEvaluation {ϑ : ℕ}
  (U₀ U₁ : Fin (2 ^ ϑ) → (ι → A)) (r : Fin ϑ → F) (r_affine_combine : F) : (ι → A) :=
  tensorCombine (u := affineLineEvaluation (F := F) U₀ U₁ r_affine_combine) (r := r)

def splitHalfRowWiseInterleavedWords {ϑ : ℕ} (u : Fin (2 ^ (ϑ + 1)) → (ι → A)) :
  (Fin (2 ^ (ϑ)) → (ι → A)) × (Fin (2 ^ (ϑ)) → (ι → A)) := by
  have h_pow_lt: 2 ^ (ϑ) < 2 ^ (ϑ + 1) := by
    apply Nat.pow_lt_pow_succ (by omega)
  let u₀ : Fin (2 ^ (ϑ)) → (ι → A) := fun rowIdx => u ⟨rowIdx, by omega⟩
  let u₁ : Fin (2 ^ (ϑ)) → (ι → A) := fun rowIdx => u ⟨rowIdx + 2 ^ (ϑ), by
    calc _ < 2 ^ (ϑ) + 2 ^ (ϑ) := by omega
      _ = 2 ^ (ϑ + 1) := by omega
  ⟩
  use u₀, u₁

def mergeHalfRowWiseInterleavedWords {ϑ : ℕ}
  (u₀ : Fin (2 ^ (ϑ)) → (ι → A))
  (u₁ : Fin (2 ^ (ϑ)) → (ι → A)) :
  Fin (2 ^ (ϑ + 1)) → (ι → A) := fun k =>
    if hk : k.val < 2 ^ ϑ then
      u₀ ⟨k, by omega⟩
    else
      u₁ ⟨k - 2 ^ ϑ, by omega⟩

omit [Fintype ι] [Nonempty ι] [Fintype A] [DecidableEq A] [AddCommMonoid A] in
lemma eq_splitHalf_iff_merge_eq {ϑ : ℕ}
  (u : Fin (2 ^ (ϑ + 1)) → (ι → A))
  (u₀ : Fin (2 ^ (ϑ)) → (ι → A))
  (u₁ : Fin (2 ^ (ϑ)) → (ι → A)) :
  (u₀ = splitHalfRowWiseInterleavedWords (u := u).1
  ∧ u₁ = splitHalfRowWiseInterleavedWords (u := u).2)
  ↔ mergeHalfRowWiseInterleavedWords u₀ u₁ = u := by
  constructor
  · intro h_split_eq_merge
    funext rowIdx
    -- funext colIdx
    simp only [mergeHalfRowWiseInterleavedWords]
    simp only [splitHalfRowWiseInterleavedWords] at h_split_eq_merge
    by_cases hk : rowIdx.val < 2 ^ ϑ
    · simp only [hk, ↓reduceDIte]
      have h_eq := h_split_eq_merge.1
      simp only [funext_iff] at h_eq
      let res := h_eq ⟨rowIdx, by omega⟩
      simp only [←funext_iff] at res
      exact res
    · simp only [hk, ↓reduceDIte]
      have h_eq := h_split_eq_merge.2
      simp only [funext_iff] at h_eq
      let res := h_eq ⟨rowIdx - 2 ^ ϑ, by omega⟩
      simp only [←funext_iff] at res
      rw! (castMode:=.all) [Nat.sub_add_cancel (h := by omega)] at res
      exact res
  · intro h_merge_eq_split
    simp only [splitHalfRowWiseInterleavedWords]
    unfold mergeHalfRowWiseInterleavedWords at h_merge_eq_split
    rw [funext_iff] at h_merge_eq_split
    constructor
    · funext rowIdx
      let res := h_merge_eq_split ⟨rowIdx, by omega⟩
      simp only [Fin.is_lt, ↓reduceDIte, Fin.eta] at res
      exact res
    · funext rowIdx
      let res := h_merge_eq_split ⟨rowIdx + 2 ^ ϑ, by omega⟩
      simp only [add_lt_iff_neg_right, not_lt_zero', ↓reduceDIte, add_tsub_cancel_right,
        Fin.eta] at res
      exact res

omit [Nonempty ι] [Fintype A] [DecidableEq A] [Fintype F] in
/-- NOTE: This could be generalized to 2 * N instead of 2 ^ (ϑ + 1).
Also, this can be proved for `↔` instead of `→`. -/
theorem CA_split_rowwise_implies_CA
    {ϑ : ℕ} (u : Fin (2 ^ (ϑ + 1)) → (ι → A)) (e : ℕ) :
    let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
    let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
    (HLC.toInterleavedCode (Fin (2 ^ (ϑ)))).correlatedAgreement₂ (⊛|U₀) (⊛|U₁) e
      → HLC.correlatedAgreement u e := by
-- 1. Unfold definitions
  unfold HLinearCode.correlatedAgreement HLinearCode.correlatedAgreement₂
  simp only
  set U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
  set U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
  simp only [HLinearCode.correlatedAgreement]
  conv_lhs => rw [closeToCode_iff_closeToCodeword]
  intro hCA_split_rowwise
  rcases hCA_split_rowwise with ⟨vSplit, hvSplit_mem, hvSplit_dist_le_e⟩
  -- ⊢ Δ₀(⊛|u, ↑(HLinearCode.toInterleavedCode (Fin (2 ^ (ϑ + 1))) HLC)) ≤ ↑e
  rw [closeToWord_iff_exists_possibleDisagreeCols] at hvSplit_dist_le_e
  rcases hvSplit_dist_le_e with ⟨D, hD_card_le_e, h_agree_outside_D⟩
  rw [closeToCode_iff_closeToCodeword (u := ⊛|u) (e := e)
    (C :=(HLinearCode.toInterleavedCode (Fin (2 ^ (ϑ + 1))) HLC))]
  simp_rw [closeToWord_iff_exists_possibleDisagreeCols]
  let VSplit_rowwise := transposeFinMap vSplit
  let VSplit₀_rowwise := transposeFinMap (VSplit_rowwise 0)
  let VSplit₁_rowwise := transposeFinMap (VSplit_rowwise 1)
  let v_rowwise_finmap : Fin (2 ^ (ϑ + 1)) → (ι → A) :=
    mergeHalfRowWiseInterleavedWords VSplit₀_rowwise VSplit₁_rowwise
  let v_IC := ⊛| v_rowwise_finmap
  use v_IC
  constructor
  · -- v_IC ∈ ↑(HLinearCode.toInterleavedCode (Fin (2 ^ (ϑ + 1))) HLC)
    simp only [SetLike.mem_coe, mem_HLinearInterleavedCode]
    intro rowIdx
    have h_vSplit_rows_mem : ∀ (i : Fin 2) (j : Fin (2 ^ ϑ)), (fun col ↦ vSplit col i j) ∈ HLC := by
      unfold HLinearCode.toInterleavedCode at hvSplit_mem
      simp only [SetLike.mem_coe] at hvSplit_mem
      intro i
      specialize hvSplit_mem i
      exact hvSplit_mem
    -- Now we prove `v_rowwise_finmap rowIdx ∈ HLC` by cases on rowIdx.
    dsimp only [v_IC]
    by_cases hk : rowIdx.val < 2 ^ ϑ
    · -- Case 1: rowIdx is in the first half
      -- exact h_vSplit_rows_mem 0 ⟨rowIdx.val, hk⟩
      let hRes₀ := h_vSplit_rows_mem 0 ⟨rowIdx.val, hk⟩
      simp only [Fin.isValue] at hRes₀
      convert hRes₀
      rename_i colIdx
      -- ⊢ getRow (⊛|v_rowwise_finmap) rowIdx colIdx = vSplit colIdx 0 ⟨↑rowIdx, hk⟩
      unfold interleaveWords v_rowwise_finmap mergeHalfRowWiseInterleavedWords VSplit₀_rowwise
        transposeFinMap VSplit_rowwise transposeFinMap getRow transposeFinMap
      simp only [hk, ↓reduceDIte, Fin.isValue]
    · -- Case 2: rowIdx is in the second half
      let hRes₁ := h_vSplit_rows_mem 1 ⟨rowIdx.val - 2 ^ ϑ, by omega⟩
      simp only [Fin.isValue] at hRes₁
      convert hRes₁
      rename_i colIdx
      -- ⊢ getRow (⊛|v_rowwise_finmap) rowIdx colIdx = vSplit colIdx 1 ⟨↑rowIdx - 2 ^ ϑ, by omega⟩
      unfold interleaveWords v_rowwise_finmap mergeHalfRowWiseInterleavedWords VSplit₁_rowwise
        transposeFinMap VSplit_rowwise transposeFinMap getRow transposeFinMap
      simp only [hk, ↓reduceDIte, Fin.isValue]
    -- END OF MODIFIED SECTION
  · use D
    constructor
    · exact hD_card_le_e
    · intro colIdx h_colIdx_notin_D
      funext rowIdx
      simp only [interleaveWords]
      dsimp only [v_IC]
      have hRes := h_agree_outside_D colIdx (h_colIdx_notin_D)
      -- hRes : (⊛|finMapTwoWords (⊛|U₀) (⊛|U₁)) colIdx = vSplit colIdx
      -- ⊢ u rowIdx colIdx = (⊛|v_rowwise_finmap) colIdx rowIdx
      simp_rw [funext_iff] at hRes
      unfold finMapTwoWords interleaveWords at hRes
      by_cases hk : rowIdx.val < 2 ^ ϑ
      · -- Case 1: We are in the "U₀" half
        unfold interleaveWords v_rowwise_finmap mergeHalfRowWiseInterleavedWords VSplit₀_rowwise
          transposeFinMap VSplit_rowwise transposeFinMap
        simp only [hk, ↓reduceDIte, Fin.isValue]
        -- ⊢ u rowIdx colIdx = vSplit colIdx 0 ⟨↑rowIdx, ⋯⟩
        have hRes₀ := hRes 0 ⟨rowIdx, by omega⟩
        simp only [Fin.isValue] at hRes₀
        exact hRes₀
      · -- Case 2: We are in the "U₁" half
        unfold interleaveWords v_rowwise_finmap mergeHalfRowWiseInterleavedWords VSplit₁_rowwise
          transposeFinMap VSplit_rowwise transposeFinMap
        simp only [hk, ↓reduceDIte, Fin.isValue]
        -- ⊢ u rowIdx colIdx = vSplit colIdx 1 ⟨↑rowIdx - 2 ^ ϑ, ⋯⟩
        have hRes₁ := hRes 1 ⟨rowIdx - 2 ^ ϑ, by omega⟩
        simp only [Fin.isValue] at hRes₁
        ---
        dsimp only [splitHalfRowWiseInterleavedWords, Fin.isValue, U₁] at hRes₁
        rw! (castMode:=.all) [Nat.sub_add_cancel (h := by omega)] at hRes₁
        exact hRes₁

omit [Fintype ι] [Nonempty ι] [Fintype A] [DecidableEq A] [Fintype F] in
/-- `[⊗_{i=0}^{ϑ-1}(1-r_i, r_i)] · [ - u₀ - ; ... ; - u_{2^ϑ-1} - ]`
`- [⊗_{i=0}^{ϑ-2}(1-r_i, r_i)] · ([(1-r_{ϑ-1}) · U₀] + [r_{ϑ-1} · U₁])` -/
lemma tensorCombine_recursive_form
  {ϑ : ℕ} (u : Fin (2 ^ (ϑ + 1)) → (ι → A)) (r : Fin (ϑ + 1) → F) :
  let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
  let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
  let r_init : Fin (ϑ) → F := Fin.init r
  tensorCombine (u:=u) (r:=r) =
  tensorCombine (ϑ := ϑ) (u:=
    affineLineEvaluation (F := F) (u₀ := U₀) (u₁ := U₁) (r := r (Fin.last ϑ))) (r:=r_init) := by
  -- 1. Unfold definitions and prove equality component-wise for each column index.
  funext colIdx
  simp only [tensorCombine]
  have h_2_pow_ϑ_succ : 2 ^ (ϑ + 1) = 2 ^ (ϑ) + 2 ^ (ϑ) := by
    exact Nat.two_pow_succ ϑ
  rw! (castMode := .all) [h_2_pow_ϑ_succ]
  conv_lhs => -- split the sum in LHS over (fin (2 ^ (ϑ + 1))) into two sums over (fin (2 ^ (ϑ)))
    rw [Fin.sum_univ_add (a := 2 ^ (ϑ)) (b := 2 ^ (ϑ))]
    simp only [Fin.natAdd_eq_addNat]
    -- 2. Simplify LHS using definitions of U₀ and U₁
  simp only [splitHalfRowWiseInterleavedWords]
  -- We also need to unfold U₀ and U₁ on the RHS.
  -- 3. Unfold RHS and distribute the sum
  simp only [affineLineEvaluation, Pi.add_apply, Pi.smul_apply, smul_add, smul_smul,
    sum_add_distrib]
  -- 4. Combine sums on LHS & RHS
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  -- 5. Show equality inside the sum
  apply Finset.sum_congr rfl
  intro i _ -- `i` is the row index `Fin (2 ^ ϑ)`
  simp_rw [eqRec_eq_cast]
  rw! [←Fin.cast_eq_cast (h := by omega)]
  -- 6. Prove the two core tensorProduct identities
  -- These are the key `Nat.getBit` facts.
  let r_init := Fin.init r
  -- 7. Apply the identities to finish the proof
  -- The goal is now `... • U₀ i colIdx + ... • U₁ i colIdx = ... • U₀ i colIdx + ... • U₁ i colIdx`
  have h_fin_cast_castAdd: Fin.cast (eq := by omega) (i := Fin.castAdd (n := 2 ^ ϑ)
    (m := 2 ^ ϑ) i) = (⟨i, by omega⟩ : Fin (2 ^ (ϑ + 1))) := by rfl
  have h_fin_cast_castAdd_2: Fin.cast (eq := by omega)
    (i := i.addNat (2 ^ ϑ)) = (⟨i + 2 ^ ϑ, by omega⟩ : Fin (2 ^ (ϑ + 1))) := by rfl
  rw [h_fin_cast_castAdd, h_fin_cast_castAdd_2]

  have h_getLastBit : Nat.getBit (Fin.last ϑ) i = 0 := by
    have h := Nat.getBit_of_lt_two_pow (a := i) (k := Fin.last ϑ)
    simp only [Fin.val_last, lt_self_iff_false, ↓reduceIte] at h
    exact h
  have h_i_and_2_pow_ϑ : i.val &&& (2 ^ ϑ) = 0 := by
    apply Nat.and_two_pow_eq_zero_of_getBit_0 (n := i) (i := ϑ)
    exact h_getLastBit
  have h_i_add_2_pow_ϑ := Nat.sum_of_and_eq_zero_is_xor (n := i.val)
    (m := 2 ^ ϑ) (h_n_AND_m:=h_i_and_2_pow_ϑ)

  have h_getLastBit_add_pow_2 : Nat.getBit (Fin.last ϑ) (i + 2 ^ ϑ) = 1 := by
    rw [h_i_add_2_pow_ϑ]; rw [Nat.getBit_of_xor]
    rw [h_getLastBit]; rw [Nat.getBit_two_pow]
    simp only [Fin.val_last, BEq.rfl, ↓reduceIte, Nat.zero_xor]

  have h_tensor_split_0 :
    tensorProduct r ⟨i, by omega⟩ = tensorProduct r_init i * (1 - r (Fin.last ϑ)) := by
    dsimp only [tensorProduct]
    rw [Fin.prod_univ_castSucc]
    simp_rw [h_getLastBit]
    simp only [Fin.coe_castSucc, ↓reduceIte]
    congr 1

  have h_tensor_split_1 :
    tensorProduct r ⟨i + 2 ^ ϑ, by omega⟩ = tensorProduct r_init i * (r (Fin.last ϑ)) := by
    dsimp only [tensorProduct]
    rw [Fin.prod_univ_castSucc]
    simp_rw [h_getLastBit_add_pow_2]
    simp only [Fin.coe_castSucc, one_ne_zero, ↓reduceIte]
    congr 1
    apply Finset.prod_congr rfl
    intro x hx_univ-- index of the product
    rw [h_i_add_2_pow_ϑ]
    simp_rw [Nat.getBit_of_xor, Nat.getBit_two_pow]
    simp only [beq_iff_eq, Nat.xor_eq_zero]
    have h_x_ne_ϑ: ϑ ≠ x.val := by omega
    simp only [h_x_ne_ϑ, ↓reduceIte]
    rfl
  rw [h_tensor_split_0, h_tensor_split_1]

/--
Definition 2.3. We say that `C ⊂ F^n` features tensor-style proximity gaps
with respect to the proximity parameter `e` and the false witness bound `ε` if,
for each `ϑ ≥ 1` and each list of words `u_0, ..., u_{2^ϑ-1}` in `F^n`,
if `Pr_{(r_0, ..., r_{ϑ-1}) ∈ F^ϑ} [`
      `d( [⊗_{i=0}^{ϑ-1}(1-r_i, r_i)] · [ -     u_0     - ]`
                                        `[     ⋮        ]`
                                        `[ - u_{2^ϑ-1} - ] , C) ≤ e] > ϑ · ε/q`
holds, then `d^{2^ϑ}((u_i)_{i=0}^{2^ϑ-1}, C^{2^ϑ}) ≤ e` also does. -/
def tensorStyleProximityGap (e : ℕ) (ε : ℕ)
  (ϑ : ℕ) (u : Fin (2 ^ ϑ) → (ι → A)) :=
  (Pr_{let r ← $ᵖ (Fin ϑ → F)}[ -- This syntax only works with (A : Type 0)
        Δ₀(tensorCombine (u:=u) (r:=r), HLC) ≤ e
      ] > (ϑ * ε: ℝ≥0) / (Fintype.card F : ℝ≥0)) →
      HLC.correlatedAgreement u e --  correlated agreement

structure TensorStyleProximityGaps (e : ℕ) (ε : ℕ) where
  gap_property : ∀ {ϑ : ℕ} (u : Fin (2 ^ ϑ) → (ι → A)),
    (ϑ > 0) →
    tensorStyleProximityGap HLC e ε ϑ u

omit [Fintype ι] [Nonempty ι] [Fintype A] [DecidableEq A] [Fintype F] in
lemma tensorCombine₁_eq_affineLineEvaluation -- ϑ = 1 case
  (u : Fin (2) → (ι → A)):
  ∀ (r : Fin 1 → F),
  tensorCombine (u:=u) (r:=r) = affineLineEvaluation (F := F) (u₀ := u 0) (u₁ := u 1) (r 0) := by
  intro r
  unfold tensorCombine affineLineEvaluation tensorProduct
  simp only [Nat.reducePow, Fin.sum_univ_two, Fin.isValue]
  ext colIdx
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, Fin.val_eq_zero, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, Nat.getBit_zero_eq_zero, ↓reduceIte, prod_singleton, Nat.mod_succ,
    Nat.getBit_zero_eq_self (n := 1) (h_n := by omega), one_ne_zero, Pi.add_apply, Pi.smul_apply]

end TensorProximityGapDefinitions

section MainResults
variable {F : Type} [CommRing F] [Fintype F] [NoZeroDivisors F] [DecidableEq F]
  -- switch to Type for `Pr_{...}[...]` usage
  {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A] [Module.Free F A]
  -- Semiring.toModule (R := A) => Module A A, plus Ring A for `RS code` theorems?
variable (HLC : HLinearCode ι F A) [Nontrivial HLC]

instance : NoZeroSMulDivisors (R := F) (M := A) := Module.Free.noZeroSMulDivisors F A

instance : NoZeroSMulDivisors (R := F) (M := ι → A) := _root_.Function.noZeroSMulDivisors

/-!
## Section 3: Main Results
-/

variable {m : Nat} -- Interleaving factor > 0 (Proof uses m>1 later)
variable {e ε : ℕ} -- Proximity parameter and false witness bound

/-- The set R* of parameters `r` for which `Uᵣ` is e-close to the interleaved code C^m
i.e. `R* := {r ∈ F | d^m(Uᵣ, C^m) ≤ e}` -/
def R_star (U₀ U₁ : ι → (Fin m) → A) : Finset F :=
  Finset.filter (fun r : F =>
    let Uᵣ : ι → (Fin m) → A := affineLineEvaluation U₀ U₁ r
    let C_m : CodewordSpace ι (Fin m → A) := HLC.toInterleavedCode (Fin m)
    Δ₀(Uᵣ, C_m) ≤ e
  ) Finset.univ

/-- The set D = Δ^{2m}(U, V), columns where U₀≠V₀ or U₁≠V₁. -/
def disagreementSet (U₀ U₁ V₀ V₁ : ι → κ → A) : Finset ι :=
  Finset.filter (fun colIdx => (U₀ colIdx ≠ V₀ colIdx) ∨ (U₁ colIdx ≠ V₁ colIdx)) Finset.univ

/-- The set `R** = {(r, j) ∈ R* × {0..n-1} | (Uᵣ)ʲ = (Vᵣ)ʲ}.` -/
def R_star_star (U₀ U₁ V₀ V₁ : ι → (Fin m) → A) : Finset (F × ι) :=
  (R_star HLC (m := m) (e := e) U₀ U₁) ×ˢ (Finset.univ (α := ι)) |>.filter (fun (r, j) =>
    let Uᵣ := affineLineEvaluation U₀ U₁ r
    let Vᵣ := affineLineEvaluation V₀ V₁ r
    Uᵣ j = Vᵣ j)

omit [Nonempty ι] [Fintype A] [AddCommGroup A] in
open Classical in
/-- Row-wise distance is bounded by interleaved distance.
i.e. `d((U)ᵢ, (M)ᵢ) ≤ d^m(U, M)` -/
lemma dist_row_le_dist_ToInterleavedWord (U : ι → (κ → A)) (M : ι → (κ → A)) (rowIdx : κ) :
    -- instDecidableEqInterleavedWordRow requires Classicial
    Δ₀(getRow U rowIdx, getRow M rowIdx) ≤ Δ₀(U, M) := by
  apply Finset.card_le_card
  refine monotone_filter_right univ ?_
  refine Pi.le_def.mpr ?_
  intro colIdx
  by_cases hDiffCell : getRow U rowIdx colIdx
    ≠ getRow M rowIdx colIdx
  · have hDiffCol : U colIdx ≠ M colIdx := by
      by_contra hEqCol
      simp only [getRow, transposeFinMap, ne_eq] at hDiffCell
      exact hDiffCell (congrFun hEqCol rowIdx)
    simp only [ne_eq, hDiffCell, not_false_eq_true, hDiffCol, le_refl]
  · by_cases hDiffCol : U colIdx ≠ M colIdx
    · simp only [hDiffCell, ne_eq, hDiffCol, not_false_eq_true, le_Prop_eq, implies_true]
    · simp only [hDiffCell, hDiffCol, le_refl]

omit [Fintype F] [Nonempty ι] [Fintype A] [NoZeroDivisors F] [DecidableEq F]
  [Module.Free F A] [Nontrivial ↥HLC] in
/-- Helper Lemma relating row distance to interleaved distance (as derived from DG25):
  `d((Uᵣ)ᵢ, C) ≤ d^m(Uᵣ, C^m)` -/
lemma dist_row_le_dist_ToInterleavedCode (U : ι → (Fin m) → A) :
    ∀ (rowIdx : Fin m), Δ₀((getRow U rowIdx), HLC)
      ≤ Δ₀(U, HLC.toInterleavedCode (κ := Fin m)) := by
  intro i
  set C_m := HLC.toInterleavedCode (Fin m)
  let d_To_interleaved := Code.distFromCode (u := U) (C := C_m)
  -- There exists M achieving this distance e_int
  have h_exists : ∃ M ∈ C_m, Δ₀(U, M) = d_To_interleaved := exists_closest_codeword U ↑C_m
  rcases h_exists with ⟨M, hM_mem, hM_dist⟩

  let Uᵢ := getRow U i
  let Mᵢ := getRowOfInterleavedCodeword HLC M i hM_mem
  -- We know d(Uᵢ, C) ≤ d(Uᵢ, Mᵢ) because Mᵢ ∈ C (from h_rows M hM_mem i)
  have dist_le_dist : Δ₀(Uᵢ, HLC) ≤ Δ₀(Uᵢ, Mᵢ) := by
    apply csInf_le' -- Using sInf property
    --  ⊢ ↑Δ₀(Uᵢ, Mᵢ) ∈ {d | ∃ v ∈ ↑HLC, ↑Δ₀(Uᵢ, v) ≤ d}
    simp only [SetLike.mem_coe, Set.mem_setOf_eq, Nat.cast_le]
    -- ⊢ ∃ v ∈ HLC, Δ₀(Uᵢ, v) ≤ Δ₀(Uᵢ, Mᵢ)
    use Mᵢ
    simp only [SetLike.coe_mem, le_refl, and_self]
  apply le_trans dist_le_dist
  -- ⊢ ↑Δ₀(Uᵢ, ↑Mᵢ) ≤ Δ₀(U, ↑C_m)

  have h_dist_row_le_dist_interleaved : Δ₀(Uᵢ, Mᵢ) ≤ Δ₀(U, M) := by
    simp only [Uᵢ, Mᵢ]
    simp only [getRowOfInterleavedCodeword]
    -- can't use exact due to problem in DecidableEq instanct
    convert dist_row_le_dist_ToInterleavedWord U M i

  calc
    (Δ₀(Uᵢ, Mᵢ): ℕ∞) ≤ (Δ₀(U, M): ℕ∞) :=
      ENat.coe_le_coe.mpr h_dist_row_le_dist_interleaved
    _ ≤ Δ₀(U, C_m) := le_of_eq hM_dist

/-- Extracts the constructed codewords V₀, V₁ and their agreement properties.
Hypotheses: 1. more than ε affine combinations Uᵣ are close to C^m (`hR_star_card`),
2. the base code C features proximity gaps for affine lines (`hC_gap`)
=> This function constructs the corresponding `interleaved codewords` `V₀` and `V₁` in `C^m`
that exhibit correlated agreement with `U₀` and `U₁` row-by-row respectively.
It returns a tuple containing:
- `V₀`, `V₁` : Codewords in `C^m`
- `hRowWise_pair_CA`: `Δ₀((u₀ := getRow U₀ rowIdx) ⊛₂ (u₁ := getRow U₁ rowIdx),`
                          `(v₀ := getRow V₀ rowIdx) ⊛₂ (v₁ := getRow V₁ rowIdx)) ≤ e`
-/
def constructInterleavedCodewordsAndRowWiseCA
  (U₀ U₁ : ι → (Fin m) → A)
  (hC_gap : ProximityGapAffineLines HLC e ε)
  (hR_star_card : (R_star HLC (m := m) (e := e) U₀ U₁).card > ε) :
  Σ' (V₀ V₁ : HLC.toInterleavedCode (Fin m)), -- Σ' creates a dependent tuple
    ∀ rowIdx, HLinearCode.pairCorrelatedAgreement (u₀ := getRow U₀ rowIdx)
      (u₁ := getRow U₁ rowIdx) (v₀ := getRow V₀ rowIdx) (v₁ := getRow V₁ rowIdx) e := by
  let V₀₁ : (rowIdx: Fin m)
    → Σ' (v₀ v₁ : HLC), HLinearCode.pairCorrelatedAgreement (u₀ := getRow U₀ rowIdx)
    (u₁ := getRow U₁ rowIdx) (v₀ := v₀) (v₁ := v₁) e := fun rowIdx => by
    set u₀ := getRow U₀ rowIdx;
    set u₁ := getRow U₁ rowIdx
    -- Need: Δ₀(u₀ ⊛₂ u₁, v₀ ⊛₂ v₁) ≤ e, this requires { r | (1 - r) • u₀ + r • u₁ ∈ C} > ε,
      -- which can be derived from hR_star_card
    -- For any row i, R_star_card implies the proximity gap property applies to that row
    have h_P_affineCombineRow:
      (Pr_{ let r ←$ᵖ F }[ -- Probability notation
        (Δ₀(affineLineEvaluation (F := F) u₀ u₁ r, HLC) ≤ e: Prop)
      ] > ((ε: ℝ≥0) / (Fintype.card F : ℝ≥0))) := by
      -- Goal: Show probability > ε / q
      -- We know: card R* > ε, where R* = {r | Δ₀(Uᵣ, C^m) ≤ e}
      -- Let R_line = {r | Δ₀((Uᵣ)ᵢ, C) ≤ e}
      -- We proved earlier: R* ⊆ R_line
      -- So, card R_line ≥ card R* > ε
      let R_star_set := R_star HLC (m := m) (e := e) U₀ U₁
      let R_line_set := Finset.filter (fun r =>
          Δ₀(affineLineEvaluation (F := F) u₀ u₁ r, HLC) ≤ e) Finset.univ
      -- Prove R* ⊆ R_line
      have R_star_subset : R_star_set ⊆ R_line_set := by
        intro r hr_mem
        simp only [R_star, mem_filter, mem_univ, true_and, R_star_set] at hr_mem
        simp only [R_line_set, Finset.mem_filter, Finset.mem_univ, true_and]
        -- Use dist_row_le_dist_ToInterleavedCode
        let Uᵣ := affineLineEvaluation U₀ U₁ r
        have h_dist_le := dist_row_le_dist_ToInterleavedCode HLC Uᵣ rowIdx
        have h_row_eq : affineLineEvaluation u₀ u₁ r = getRow Uᵣ rowIdx := by
          ext j; simp only [affineLineEvaluation, Pi.add_apply, Pi.smul_apply, getRow,
            transposeFinMap, affineLineEvaluation, Uᵣ]
          have h_u₀_j : u₀ j = U₀ j rowIdx := by rfl
          have h_u₁_j : u₁ j = U₁ j rowIdx := by rfl
          rw [h_u₀_j, h_u₁_j]
        rw [←h_row_eq] at h_dist_le
        exact le_trans h_dist_le hr_mem
      -- Use cardinality argument
      have h_card_line_gt_eps : R_line_set.card > ε :=
        lt_of_lt_of_le hR_star_card (Finset.card_le_card R_star_subset)
      -- Convert cardinality to probability: `Pr[P r] = card {r | P r} / card F`
      simp only [ENNReal.coe_natCast]
      rw [prob_uniform_eq_card_filter_div_card]
      simp only [ENNReal.coe_natCast]
      rw [gt_iff_lt]
      apply ENNReal.div_lt_div_right
      · simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]
      · exact ENNReal.natCast_ne_top (Fintype.card F)
      · exact Nat.cast_lt.mpr h_card_line_gt_eps

    -- Apply proximity gap of HLC to get correlated agreement at this row
    have h_corr_agree_row: Δ₀(u₀ ⊛₂ u₁, HLC.toInterleavedCode (Fin 2)) ≤ e :=
      hC_gap.gap_property (u₀) (u₁) (h_P_affineCombineRow)

    let V_rowIdx := pickClosestCodeword (u₀ ⊛₂ u₁) (HLC.toInterleavedCode (Fin 2))
    let v₀ := getRowOfInterleavedCodeword HLC (V_rowIdx.val) 0 (Submodule.coe_mem V_rowIdx)
    let v₁ := getRowOfInterleavedCodeword HLC (V_rowIdx.val) 1 (Submodule.coe_mem V_rowIdx)
    use v₀, v₁
    have h_dist_min := distFromPickClosestCodeword (u₀ ⊛₂ u₁) (HLC.toInterleavedCode (Fin 2))
    rw [h_dist_min] at h_corr_agree_row
    have h_v₀_interleaved_v₁ : (pickClosestCodeword (u₀ ⊛₂ u₁)
      (C := HLinearCode.toInterleavedCode (Fin 2) HLC)).val = (v₀ ⊛₂ v₁) := by
      funext colIdx rowIdx₀₁
      unfold v₀ v₁
      conv_rhs => unfold interleaveTwoWords interleaveWords finMapTwoWords
      conv_rhs => unfold getRowOfInterleavedCodeword getRow transposeFinMap
      simp only [Fin.isValue]
      by_cases h : rowIdx₀₁ = 0
      · rw [h]
      · have h' : rowIdx₀₁ = 1 := by omega
        rw [h']
    rw [h_v₀_interleaved_v₁] at h_corr_agree_row
    unfold HLinearCode.pairCorrelatedAgreement
    simp only [Nat.cast_le] at h_corr_agree_row
    exact h_corr_agree_row
  let V₀ : HLC.toInterleavedCode (Fin m) := ⟨⊛| fun (rowIdx: Fin m) ↦ (V₀₁ rowIdx).1.val, by
    apply interleaveCodewords;
    simp only [SetLike.coe_mem, implies_true]
  ⟩
  let V₁ : HLC.toInterleavedCode (Fin m) := ⟨⊛| fun (rowIdx: Fin m) ↦ (V₀₁ rowIdx).2.1.val, by
    apply interleaveCodewords;
    simp only [SetLike.coe_mem, implies_true]
  ⟩
  use V₀, V₁
  intro rowIdx
  -- HLinearCode.pairCorrelatedAgreement u₀ u₁ v₀ v₁ e
  exact (V₀₁ rowIdx).2.2 -- definitional equality of V₀ V₁ according to V₀₁

omit [Nonempty ι] [NoZeroDivisors F] [DecidableEq F] [Fintype A] [Module.Free F A] in
/-- **Lemma 3.2 (DG25): Closeness implies Closeness to Constructed Codeword**
Context:
- `C` is a linear code in `F^n` with proximity gaps for affine lines (params `e`, `ε`).
- `e` is within the unique decoding radius of `C`.
- `U₀, U₁` are ColWise-interleaved words.
- `R*` is the set of `r` in `F` such that `Uᵣ = (1-r)U₀ + rU₁` is `e`-close to `C^m`.
- `V₀, V₁` are specific codewords in `C^m` constructed row-by-row using `C`'s gap property,
  assuming `|R*| > ε`.
- `Vᵣ = (1-r)V₀ + rV₁`.
Statement: For any parameter `r` in `R*`, the matrix `Uᵣ` must be `e`-close to the codeword `Vᵣ`.
 Lemma 3.2: Given a linear code `C ⊂ F^n` with proximity gaps for affine lines
(parameters `e`, `ε`), its `m`-fold interleaving `C^m`, and two matrices
`U_0`, `U_1 ∈ F^{m × n}`, let `U_r = (1-r)U_0 + rU_1` be a point on the affine line between them,
and let `R* = { r ∈ F | d^m(U_r, C^m) ≤ e }` be the set of parameters yielding points close
to the interleaved code.
-/
lemma affineWord_close_to_affineInterleavedCodeword
  (U₀ U₁ : ι → (Fin m) → A)
  (he : e ∈ Finset.range (HLinearCode.uniqueDecodingRadius (HLC := HLC)))
  (hC_gap : ProximityGapAffineLines HLC e ε)
  (hR_star_card : (R_star HLC (m := m) (e := e) U₀ U₁).card > ε) :
    let ⟨V₀, V₁, _⟩ := constructInterleavedCodewordsAndRowWiseCA HLC U₀ U₁ hC_gap hR_star_card
    ∀ (r : R_star HLC (m := m) (e := e) U₀ U₁), -- Δ₀ (Uᵣ, Vᵣ) ≤ e
      Δ₀(affineLineEvaluation (F := F) U₀ U₁ r, affineLineEvaluation (F := F) V₀ V₁ r) ≤ e := by
-- 1. Setup: Define V₀, V₁, Vᵣ, r, Uᵣ
  let ⟨V₀, V₁, h_row_agreement⟩ :=
    constructInterleavedCodewordsAndRowWiseCA HLC U₀ U₁ hC_gap hR_star_card
  intro r_sub
  let r := r_sub.val
  set Uᵣ := affineLineEvaluation (F := F) U₀ U₁ r
  set Vᵣ := affineLineEvaluation (F := F) V₀.val V₁.val r

  -- 2. By definition of R*, there exists *some* codeword Vᵣ* close to Uᵣ
  have h_r_in_R_star := r_sub.property
  simp only [R_star, Finset.mem_filter, Finset.mem_univ, true_and] at h_r_in_R_star
  -- h_r_in_R_star is: Δ₀(Uᵣ, HLC.toInterleavedCode (Fin m)) ≤ e
  -- Use `exists_closest_codeword` to get this Vᵣ*
  let Vᵣ_star := pickClosestCodeword Uᵣ (HLC.toInterleavedCode (Fin m))
  have hVᵣ_star_dist : Δ₀(Uᵣ, Vᵣ_star) = Δ₀(Uᵣ, HLC.toInterleavedCode (Fin m)) := by
    dsimp only [Vᵣ_star]
    rw [distFromPickClosestCodeword]

  have h_dist_Uᵣ_Vᵣ_star_le_e : Δ₀(Uᵣ, Vᵣ_star) ≤ e := by
    rw [←ENat.coe_le_coe, hVᵣ_star_dist]; exact h_r_in_R_star

  -- We must show Vᵣ* = Vᵣ. We do this row-by-row.
  -- Goal is Δ₀(Uᵣ, Vᵣ) ≤ e. We will prove Vᵣ = Vᵣ_star, then rw.
  have h_Vᵣ_eq_Vᵣ_star : Vᵣ = Vᵣ_star.val := by
    rw [interleavedWord_eq_iff_allRowsEq]
    intro rowIdx
    -- Get the i-th rows of Vᵣ and Vᵣ*
    set Vᵣ_i := getRow Vᵣ rowIdx
    set Vᵣ_star_i := getRow Vᵣ_star.val rowIdx
    -- ⊢ Vᵣ_i = Vᵣ_star_i
    -- 3. Show (Uᵣ)ᵢ is e-close to (Vᵣ*)ᵢ
    have h_dist_Uᵣi_Vᵣstari : Δ₀(getRow Uᵣ rowIdx, Vᵣ_star_i) ≤ e := by
      have h_Δ₀_getrow_Uᵣ_Vᵣ := dist_row_le_dist_ToInterleavedWord Uᵣ Vᵣ_star.val rowIdx
      apply le_trans (h_Δ₀_getrow_Uᵣ_Vᵣ)
      exact h_dist_Uᵣ_Vᵣ_star_le_e

    -- 4. Show (Uᵣ)ᵢ is e-close to (Vᵣ)ᵢ
    -- Get the row-wise agreement for row i from the constructor
    have h_agree_i := h_row_agreement rowIdx
    unfold HLinearCode.pairCorrelatedAgreement at h_agree_i
    -- h_agree_i : Δ₀(getRow U₀ i ⊛₂ getRow U₁ i, getRow V₀.val i ⊛₂ getRow V₁.val i) ≤ e

    -- Show (Vᵣ)ᵢ is the affine combo of the rows of V₀, V₁
    have h_Vᵣ_i_eq_affine : Vᵣ_i =
      affineLineEvaluation (getRow V₀.val rowIdx) (getRow V₁.val rowIdx) r := by
      ext j; simp only [getRow, affineLineEvaluation, transposeFinMap, Pi.add_apply,
        Pi.smul_apply, Vᵣ_i, Vᵣ]

    -- Show (Uᵣ)ᵢ is the affine combo of the rows of U₀, U₁
    have h_Uᵣ_i_eq_affine : getRow Uᵣ rowIdx
      = affineLineEvaluation (getRow U₀ rowIdx) (getRow U₁ rowIdx) r := by
      ext j; simp only [getRow, transposeFinMap, affineLineEvaluation, Pi.add_apply,
        Pi.smul_apply, Uᵣ];

    -- We need Δ₀((Uᵣ)ᵢ, (Vᵣ)ᵢ) ≤ e
    have h_dist_Uᵣi_Vᵣi : Δ₀(getRow Uᵣ rowIdx, Vᵣ_i) ≤ e := by
      -- ⊢ Δ₀(getRow (affineLineEvaluation U₀ U₁ r) rowIdx, getRow Vᵣ rowIdx) ≤ e
      have h_dist_row_le_dist_interleaved := dist_row_le_dist_ToInterleavedWord Uᵣ Vᵣ rowIdx
      -- apply le_trans h_dist_row_le_dist_interleaved
      -- ⊢ Δ₀(Uᵣ, Vᵣ) ≤ e
      -- Use the correlated agreement `h_agree_i`
      rw [h_Uᵣ_i_eq_affine, h_Vᵣ_i_eq_affine]
      apply le_trans (dist_affineCombination_le_dist_interleaved₂ _ _ _ _ _)
      -- ⊢ Δ₀(getRow U₀ rowIdx ⊛₂ getRow U₁ rowIdx, getRow (↑V₀) rowIdx ⊛₂ getRow (↑V₁) rowIdx) ≤ e
      exact h_agree_i

    -- 5. Use Unique Decoding to show (Vᵣ*)ᵢ = (Vᵣ)ᵢ
    -- We need the minimum distance d of the base code C
    let d: ℕ := ‖(HLC : Set (ι → A))‖₀
    have h_d_pos : 0 < d := by
      -- Need to show d > 0. Usually codes have d ≥ 1 if not empty/trivial.
      -- Assuming d > 0 for non-trivial codes.
      rw [HLinearCode.uniqueDecodingRadius, Finset.mem_range] at he
      let res :=  Code.dist_pos_of_Nontrivial (ι := ι) (F := A) (C := HLC) (hC := by
        (expose_names; exact Set.nontrivial_coe_sort.mp inst_6))
      exact res

    -- We need 2e < d
    have h_2e_lt_d : 2 * e < d := by
      rw [HLinearCode.uniqueDecodingRadius, Finset.mem_range] at he
      have h_2e_lt_d := two_mul_unique_radius_dist_lt_d (HLC := HLC) (h_dist_pos := h_d_pos) he
      exact h_2e_lt_d
    -- Apply unique decoding:
    -- Vᵣ_star_i is a codeword because it's a row of Vᵣ_star ∈ C^m
    have hVᵣ_star_i_mem : Vᵣ_star_i ∈ HLC := by
      have hVᵣ_star := Vᵣ_star.property
      rw [mem_HLinearInterleavedCode] at hVᵣ_star
      exact hVᵣ_star rowIdx
    -- Vᵣ_i is a codeword because it's an affine combo of rows from V₀, V₁ ∈ C^m
    have hVᵣ_i_mem : Vᵣ_i ∈ HLC := by
      rw [h_Vᵣ_i_eq_affine]
      apply HLC.add_mem
      · apply HLC.smul_mem;
        exact (getRowOfInterleavedCodeword HLC V₀.val rowIdx (Submodule.coe_mem V₀)).property
      · apply HLC.smul_mem;
        exact (getRowOfInterleavedCodeword HLC V₁.val rowIdx (Submodule.coe_mem V₁)).property

    -- Apply the triangle inequality: d(Vᵣ_i, Vᵣ_star_i) ≤ d(Vᵣ_i, Uᵣ_i) + d(Uᵣ_i, Vᵣ_star_i)
    have h_dist_v_vstar : Δ₀(Vᵣ_i, Vᵣ_star_i) ≤ Δ₀(Vᵣ_i, getRow Uᵣ rowIdx)
      + Δ₀(getRow Uᵣ rowIdx, Vᵣ_star_i) := by apply hammingDist_triangle

    -- We need to convert from ℕ∞ (Δ₀) to ℕ (hammingDist) for Code.eq_of_lt_dist
    have h_dist_v_vstar_nat : hammingDist Vᵣ_i Vᵣ_star_i < d := by
      -- Convert ℕ∞ inequalities to ℕ inequalities
      have h1_nat : hammingDist (getRow Uᵣ rowIdx) Vᵣ_i ≤ e :=
        ENat.coe_le_coe.mp (ENat.coe_le_coe.mpr h_dist_Uᵣi_Vᵣi)
      have h2_nat : hammingDist (getRow Uᵣ rowIdx) Vᵣ_star_i ≤ e :=
        ENat.coe_le_coe.mp (ENat.coe_le_coe.mpr h_dist_Uᵣi_Vᵣstari)
      -- Apply triangle inequality for hammingDist
      calc
        hammingDist Vᵣ_i Vᵣ_star_i ≤ hammingDist Vᵣ_i (getRow Uᵣ rowIdx)
          + hammingDist (getRow Uᵣ rowIdx) Vᵣ_star_i := hammingDist_triangle _ _ _
        _ = hammingDist (getRow Uᵣ rowIdx) Vᵣ_i + hammingDist (getRow Uᵣ rowIdx) Vᵣ_star_i
          := by rw [hammingDist_comm]
        _ ≤ e + e := Nat.add_le_add h1_nat h2_nat
        _ = 2 * e := by rw [two_mul]
        _ < d := h_2e_lt_d

    -- Now apply unique decoding
    exact Code.eq_of_lt_dist hVᵣ_i_mem hVᵣ_star_i_mem h_dist_v_vstar_nat

  -- 8. Conclude Vᵣ = Vᵣ_star and return the distance
  rw [h_Vᵣ_eq_Vᵣ_star]
  exact h_dist_Uᵣ_Vᵣ_star_le_e

open Classical in
def R_star_star_filter_columns_in_D (U₀ U₁ : ι → (Fin m) → A)
  (V₀ V₁ : HLC.toInterleavedCode (Fin m)) (e : ℕ) (D : Finset ι) : Finset (F × ι) :=
  (R_star_star HLC (m := m) (e := e) U₀ U₁ V₀ V₁).filter (fun p => p.2 ∈ D) in

def R_star_star_filter_columns_not_in_D (U₀ U₁ : ι → (Fin m) → A)
  (V₀ V₁ : HLC.toInterleavedCode (Fin m)) (e : ℕ) (D : Finset ι) : Finset (F × ι) :=
  (R_star_star HLC (m := m) (e := e) U₀ U₁ V₀ V₁).filter (fun p => p.2 ∉ D) in

omit [Nonempty ι] [NoZeroDivisors F] [Fintype A] [DecidableEq A] [Module.Free F A]
  [Nontrivial ↥HLC] in
lemma R_star_star_eq_union (U₀ U₁ : ι → (Fin m) → A)
  (V₀ V₁ : HLC.toInterleavedCode (Fin m)) (e : ℕ) (D : Finset ι):
  (R_star_star HLC (m := m) (e := e) U₀ U₁ V₀ V₁) =
    (R_star_star_filter_columns_not_in_D HLC U₀ U₁ V₀ V₁ (e := e) D)
    ∪ (R_star_star_filter_columns_in_D HLC U₀ U₁ V₀ V₁ (e := e) D) := by
  dsimp only [R_star_star, Lean.Elab.WF.paramLet, R_star_star_filter_columns_not_in_D,
    R_star_star_filter_columns_in_D]
  rw [Finset.union_comm]
  rw [Finset.filter_union_filter_neg_eq]

omit [Nonempty ι] [NoZeroDivisors F] [DecidableEq F] [Fintype A] [DecidableEq A]
  [Module.Free F A] [Nontrivial ↥HLC] in
open Classical in
lemma disjoint_R_star_star_filter_columns_in_D_not_in_D (U₀ U₁ : ι → (Fin m) → A)
    (V₀ V₁ : HLC.toInterleavedCode (Fin m)) (e : ℕ) (D : Finset ι) :
  Disjoint (R_star_star_filter_columns_in_D HLC U₀ U₁ V₀ V₁ (e := e) D)
    (R_star_star_filter_columns_not_in_D HLC U₀ U₁ V₀ V₁ (e := e) D) := by
-- 1. Unfold the definitions to reveal the underlying `filter` structure
  unfold R_star_star_filter_columns_in_D R_star_star_filter_columns_not_in_D
  -- The goal is now `Disjoint (R_ss.filter P) (R_ss.filter (¬P))`
  apply disjoint_filter_filter_neg

omit [Nonempty ι] [NoZeroDivisors F] [DecidableEq F] [Fintype A] [Module.Free F A]
  [Nontrivial ↥HLC] in
lemma D_card_le_e_implies_interleaved_correlatedAgreement₂
  (U₀ U₁ : ι → (Fin m) → A)
  (hC_gap : ProximityGapAffineLines HLC e ε)
  (hR_star_card : (R_star HLC (m := m) (e := e) U₀ U₁).card > ε) :
    let V₀ := (constructInterleavedCodewordsAndRowWiseCA HLC U₀ U₁ hC_gap hR_star_card).1
    let V₁ := (constructInterleavedCodewordsAndRowWiseCA HLC U₀ U₁ hC_gap hR_star_card).2.1
    (disagreementSet U₀ U₁ V₀ V₁).card ≤ e
    → (HLC.toInterleavedCode (Fin m)).correlatedAgreement₂ U₀ U₁ e := by
  -- 1. Unfold definitions and simplify
  set C_m := HLC.toInterleavedCode (Fin m)
  set U_rowwise := finMapTwoWords U₀ U₁
  set U_colwise := ⊛| U_rowwise
  set C_m_2 := C_m.toInterleavedCode (Fin 2)
  -- Unfold the goal
  unfold HLinearCode.correlatedAgreement₂ HLinearCode.correlatedAgreement
  -- Goal: (let ⟨V₀, V₁, _⟩ := ... in (disagreementSet ...).card ≤ e) → (Δ₀(U_comb, C_m_2) ≤ e)
  simp only
  -- 2. Introduce the bindings and the hypothesis
  intro hDisagreeementCard_Le_e -- The assumption: (disagreementSet U₀ U₁ V₀ V₁).card ≤ e
  set V₀ := (constructInterleavedCodewordsAndRowWiseCA HLC U₀ U₁ hC_gap hR_star_card).1
  set V₁ := (constructInterleavedCodewordsAndRowWiseCA HLC U₀ U₁ hC_gap hR_star_card).2.1
  set hRowPairCA_U_V := (constructInterleavedCodewordsAndRowWiseCA
    HLC U₀ U₁ hC_gap hR_star_card).2.2
  have hD_card_le_e : #(disagreementSet U₀ U₁ V₀ V₁) ≤ e :=
    hDisagreeementCard_Le_e
  -- 3. Show LHS assumption is equal to Δ₀(U_comb, V_constructed) ≤ e
  set V_rowwise := finMapTwoWords V₀.val V₁.val
  set V_colwise := ⊛| V_rowwise
  have h_LHS_eq_dist : (disagreementSet U₀ U₁ V₀ V₁).card = Δ₀(U_colwise, V_colwise) := by
    unfold disagreementSet U_colwise V_colwise
    unfold interleaveWords U_rowwise V_rowwise hammingDist Finset.filter
    simp only [ne_eq, card_mk]
    congr 1
    congr 1
    funext colIdx
    simp only [eq_iff_iff]
    constructor
    · intro hleft
      simp only at hleft ⊢
      by_contra h_fun_eq
      rw [funext_iff] at h_fun_eq
      by_cases h_left_1: ¬U₀ colIdx = V₀.val colIdx
      · simp only [h_left_1, not_false_eq_true, true_or] at hleft
        have h_U₀_eq_V₀ := h_fun_eq 0
        simp only [finMapTwoWords] at h_U₀_eq_V₀
        exact h_left_1 h_U₀_eq_V₀
      · simp only [h_left_1, false_or] at hleft
        have h_U₁_eq_V₁ := h_fun_eq 1
        simp only [finMapTwoWords] at h_U₁_eq_V₁
        exact h_left_1 fun a ↦ hleft h_U₁_eq_V₁
    · intro h_fun_ne
      rw [funext_iff] at h_fun_ne
      rw [not_forall] at h_fun_ne
      rcases h_fun_ne with ⟨i_fin2, h_fun_ne_i⟩
      fin_cases i_fin2
      · simp only [finMapTwoWords] at h_fun_ne_i
        left
        exact h_fun_ne_i
      · simp only [finMapTwoWords] at h_fun_ne_i
        right
        exact h_fun_ne_i
  -- Our assumption `h_LHS` is now: Δ₀(U_comb, V_constructed) ≤ e
  simp_rw [h_LHS_eq_dist] at hD_card_le_e
  -- 4. Prove the RHS: Δ₀(U_comb, C_m_2) ≤ e
  -- By `correlatedAgreement_iff_closeToInterleavedCodeword`, this is equivalent
  -- to `∃ v ∈ C_m_2, Δ₀(U_comb, v) ≤ e`
  let CA_to_close := correlatedAgreement_iff_closeToInterleavedCodeword
    (HLC := HLC.toInterleavedCode (Fin m)) (κ := Fin 2) (ι := ι) (F := F)
    (A := (Fin m) → A) (e := e) (u := finMapTwoWords U₀ U₁)
  rw [Code.closeToCode_iff_closeToCodeword]

  -- ⊢ ∃ v ∈ ↑(HLinearCode.toInterleavedCode (Fin 2) (HLinearCode.toInterleavedCode (Fin m) HLC)),
  -- Δ₀(⊛|finMapTwoWords U₀ U₁, v) ≤ e
  use V_colwise
  have hVMem_IC := interleaveCodewords (u := V_rowwise) (HLC := HLC.toInterleavedCode (Fin m))
    (fun rowIdx => by
    match rowIdx with
    | ⟨0, _⟩ => exact Submodule.coe_mem V₀
    | ⟨1, _⟩ => exact Submodule.coe_mem V₁
  )
  use hVMem_IC, hD_card_le_e

omit [Nonempty ι] [NoZeroDivisors F] [DecidableEq F] [Fintype A] [DecidableEq A]
    [Module.Free F A] [Nontrivial ↥HLC] in
/-- **Lemma 3.3 (Part 1): Bound on agreeing cells outside D**
    The set of agreeing cells `(r, j)` where `j ∉ D` is exactly the
    Cartesian product of `R*` and `Dᶜ` (the columns not in D).
-/
lemma card_agreeing_cells_notin_D
    {U₀ U₁ : ι → (Fin m) → A} {V₀ V₁ : HLC.toInterleavedCode (Fin m)}
    {e : ℕ} (D : Finset ι)
    (h_D_def : D = disagreementSet U₀ U₁ V₀.val V₁.val) :
    (R_star_star_filter_columns_not_in_D HLC U₀ U₁ V₀ V₁ e D).card
    = (R_star HLC (e := e) U₀ U₁).card * (Fintype.card ι - D.card) := by
  classical
  let n := Fintype.card ι
  let D_compl := Finset.univ \ D
-- Define local abbreviations
  let n := Fintype.card ι
  let D_compl := Finset.univ \ D
  let R_s := R_star HLC (e := e) U₀ U₁
  let R_ss_not_D := R_star_star_filter_columns_not_in_D HLC U₀ U₁ V₀ V₁ e D
  -- 1. Prove that R_ss_not_D is equal to the product R_s ×ˢ D_compl
  have h_set_eq : R_ss_not_D = R_s ×ˢ D_compl := by
    -- We prove equality by showing element-wise equivalence
    ext p
    rcases p with ⟨r, j⟩
    -- Unfold all definitions
    simp only [R_star_star_filter_columns_not_in_D, R_star_star, mem_filter, mem_product, mem_univ,
      and_true, mem_sdiff, true_and, and_congr_left_iff, and_iff_left_iff_imp, R_ss_not_D, R_s,
      D_compl]
    intro j_memD r_mem_Rstar
    -- 1. Unfold the definition of `j ∉ D` to get the core equalities.
    have h_agree_at_j : U₀ j = V₀.val j ∧ U₁ j = V₁.val j := by
      -- Use the hypothesis `h_D_def` from the outer lemma
      simp only [h_D_def, disagreementSet, Finset.mem_filter, Finset.mem_univ, true_and,
                not_or, not_not] at j_memD
      -- j_memD is now `U₀ j = V₀.val j ∧ U₁ j = V₁.val j`
      exact j_memD
    -- 2. Unfold the goal (the affineLineEvaluation)
    unfold affineLineEvaluation
    simp only [Pi.add_apply, Pi.smul_apply]
    -- ⊢ (1 - r) • U₀ j + r • U₁ j = (1 - r) • ↑V₀ j + r • ↑V₁ j
    -- 3. Rewrite the goal using the equalities from h_agree_at_j
    rw [h_agree_at_j.1] -- Replaces U₀ j with V₀.val j
    rw [h_agree_at_j.2] -- Replaces U₁ j with V₁.val j
  have h_set_card_eq : R_ss_not_D.card = R_s.card * D_compl.card := by
    rw [h_set_eq]
    simp only [card_product]
  -- 2. Now calculate the cardinality using the set equality
  rw [h_set_card_eq]
  rw [Finset.card_sdiff (Finset.subset_univ D)]
  rw [Finset.card_univ]

omit [Nonempty ι] [DecidableEq F] [Fintype A] [DecidableEq A] [Nontrivial ↥HLC] in
/-- **Lemma 3.3 (Part 2): Bound on agreeing cells inside D**
For any column `j` that *is* in the disagreement set `D`, there is at most one
parameter `r` in `R*` such that the columns `Uᵣ j` and `Vᵣ j` agree.
Therefore, the total number of agreeing cells `(r, j)` with `j ∈ D` is at most `|D|`.
-/
lemma card_agreeing_cells_in_D_le
    {U₀ U₁ : ι → (Fin m) → A}
    {V₀ V₁ : HLC.toInterleavedCode (Fin m)}
    {e : ℕ} (D : Finset ι)
    (h_D_def : D = disagreementSet U₀ U₁ V₀.val V₁.val) :
    (R_star_star_filter_columns_in_D HLC U₀ U₁ V₀ V₁ e D).card ≤ D.card := by
  classical
  -- Let R_ss_in_D be the set of agreeing cells (r, j) with j ∈ D
  let R_ss_in_D := R_star_star_filter_columns_in_D HLC U₀ U₁ V₀ V₁ e D
  -- 1. The card of a set is bounded by the sum of the cardinalities of its fibers
  --    (We are "slicing" the set by its second component, the column index j)
  have h_card_eq_sum_fibers : R_ss_in_D.card
    = ∑ j ∈ D, ((R_ss_in_D.filter (fun p => p.2 = j)).card) := by
      apply Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := D)
      -- We must show that every element in R_ss_in_D maps to an element in D
      -- Goal: `Set.MapsTo (Prod.snd) R_ss_in_D D`, this means: `∀ p ∈ R_ss_in_D, p.2 ∈ D`
      intro p hp_in_Rss
      -- This is true by the very definition of R_ss_in_D!
      unfold R_ss_in_D R_star_star_filter_columns_in_D at hp_in_Rss
      simp only [coe_filter, Set.mem_setOf_eq] at hp_in_Rss
      -- hp_in_Rss is `p ∈ R_star_star ∧ p.2 ∈ D`
      exact hp_in_Rss.2
  -- 2. We prove that each fiber (for a fixed j) has cardinality at most 1
  have h_fibers_le_one_sum :
    ∑ j ∈ D, ((R_ss_in_D.filter (fun p => p.2 = j)).card) ≤ ∑ j ∈ D, 1 := by
    apply Finset.sum_le_sum
    intro j hj_in_D -- For any column j that is in the disagreement set D
    -- Goal for this term: (R_ss_in_D.filter (fun p => p.2 = j)).card ≤ 1
    apply Finset.card_le_one_iff.mpr
    -- Goal: ∀ p1 p2, p1 ∈ ... → p2 ∈ ... → p1 = p2
    -- We MUST introduce two elements (p1, p2) and their two proofs (hp1, hp2)
    intro p1 p2 hp1 hp2
    rcases p1 with ⟨r₁, j₁⟩
    rcases p2 with ⟨r₂, j₂⟩
    -- ⊢ (r₁, j₁) = (r₂, j₂)
    apply Prod.ext
    · -- Goal 1: Prove r₁ = r₂: We need to extract the agreement properties from the hypotheses
      have h1_in_Rss : (r₁, j₁) ∈ R_ss_in_D := (Finset.mem_filter.mp hp1).1
      have h1_j_eq : j₁ = j := (Finset.mem_filter.mp hp1).2
      have h2_in_Rss : (r₂, j₂) ∈ R_ss_in_D := (Finset.mem_filter.mp hp2).1
      have h2_j_eq : j₂ = j := (Finset.mem_filter.mp hp2).2
      -- Get the agreement properties from R_ss_in_D
      have h1_agree : affineLineEvaluation U₀ U₁ r₁ j = affineLineEvaluation (↑V₀) (↑V₁) r₁ j := by
        -- Unfold R_ss_in_D and R_star_star to find the agreement
        unfold R_ss_in_D R_star_star_filter_columns_in_D at h1_in_Rss
        simp only [R_star_star, mem_filter, mem_product, mem_univ, and_true] at h1_in_Rss
        rw [← h1_j_eq] -- Use j₁ = j
        exact h1_in_Rss.1.2
      have h2_agree : affineLineEvaluation U₀ U₁ r₂ j = affineLineEvaluation (↑V₀) (↑V₁) r₂ j := by
        unfold R_ss_in_D R_star_star_filter_columns_in_D at h2_in_Rss
        simp only [R_star_star, mem_filter, mem_product, mem_univ, and_true] at h2_in_Rss
        rw [← h2_j_eq] -- Use j₂ = j
        exact h2_in_Rss.1.2 -- This is the `Uᵣ j = Vᵣ j` part
      -- linear algebra argument
      let W₀ := U₀ j - V₀.val j
      let W₁ := U₁ j - V₁.val j
      have h_eq_r1 : W₀ + r₁ • (W₁ - W₀) = 0 := by
        unfold affineLineEvaluation at h1_agree
        rw [← sub_eq_zero] at h1_agree
        rw [← h1_agree]
        unfold W₀ W₁
        -- ⊢ U₀ j - ↑V₀ j + r₁ • (U₁ j - ↑V₁ j - (U₀ j - ↑V₀ j)) = ((1 - r₁) • U₀ + r₁ • U₁) j
          -- - ((1 - r₁) • ↑V₀ + r₁ • ↑V₁) j
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [sub_smul, sub_smul]; rw [smul_sub, smul_sub, smul_sub]
        simp only [one_smul]
        abel_nf
      have h_eq_r2 : W₀ + r₂ • (W₁ - W₀) = 0 := by
        unfold affineLineEvaluation at h2_agree
        rw [← sub_eq_zero] at h2_agree
        rw [← h2_agree]
        unfold W₀ W₁
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [sub_smul, sub_smul]; rw [smul_sub, smul_sub, smul_sub]
        simp only [one_smul]
        abel_nf
      have h_j_in_D : W₀ ≠ 0 ∨ W₁ ≠ 0 := by
        simp only [h_D_def, disagreementSet, ne_eq, mem_filter, mem_univ, true_and] at hj_in_D
        by_cases h₀_ne: ¬U₀ j = V₀.val j
        · left
          dsimp only [W₀]
          exact sub_ne_zero_of_ne h₀_ne
        · simp only [h₀_ne, false_or] at hj_in_D
          right
          dsimp only [W₁]
          exact sub_ne_zero_of_ne hj_in_D
      by_cases h_diff_eq_zero : W₁ - W₀ = 0
      · -- Case 1: W₁ - W₀ = 0
        have h_W₀_zero : W₀ = 0 := by rwa [h_diff_eq_zero, smul_zero, add_zero] at h_eq_r1
        have h_W₁_zero : W₁ = 0 := by
          rw [←h_diff_eq_zero, h_W₀_zero];
          exact Eq.symm (sub_zero W₁)
        by_cases h_W₀_ne_zero : W₀ ≠ 0
        · exact False.elim (h_W₀_ne_zero h_W₀_zero)
        · have h_W₁_ne_0 : W₁ ≠ 0 := by
            exact h_j_in_D.resolve_left h_W₀_ne_zero
          exact False.elim (h_W₀_ne_zero fun a ↦ h_W₁_ne_0 h_W₁_zero)
      · -- Case 2: W₁ - W₀ ≠ 0 (this is `h_diff_eq_zero : ¬W₁ - W₀ = 0`)
        -- 2 hypotheses: h_eq_r1 : W₀ + r₁ • (W₁ - W₀) = 0, h_eq_r2 : W₀ + r₂ • (W₁ - W₀) = 0
        have h_eq_both : W₀ + r₁ • (W₁ - W₀) = W₀ + r₂ • (W₁ - W₀) := by
          rw [h_eq_r1, h_eq_r2]
        have h_smul_eq : r₁ • (W₁ - W₀) = r₂ • (W₁ - W₀) :=
          (add_right_inj W₀).mp h_eq_both
        have h_sub_smul_eq_zero : (r₁ - r₂) • (W₁ - W₀) = 0 := by
          rw [sub_smul, sub_eq_zero]
          exact h_smul_eq
        rw [smul_eq_zero] at h_sub_smul_eq_zero
        have h_r_sub_eq_zero : r₁ - r₂ = 0 := by
          exact h_sub_smul_eq_zero.resolve_right h_diff_eq_zero
        exact sub_eq_zero.mp h_r_sub_eq_zero
    · -- Goal 2: Prove j₁ = j₂: This follows directly from the fiber proofs
      have h1_j_eq : j₁ = j := (Finset.mem_filter.mp hp1).2
      have h2_j_eq : j₂ = j := (Finset.mem_filter.mp hp2).2
      rw [h1_j_eq, h2_j_eq]
  -- 3. Chain the inequalities: R_ss_in_D.card ≤ (∑ j in D, 1) ≤ D.card
  simp only [sum_const, smul_eq_mul, mul_one] at h_fibers_le_one_sum
  exact le_trans (Nat.le_of_eq h_card_eq_sum_fibers) h_fibers_le_one_sum

omit [Nonempty ι] [Fintype A] [Nontrivial ↥HLC] in
/-- **Lemma 3.3 (DG25): Upper Bound on R** Cardinality**
Context:
- `U₀, U₁` are columnWise words; `V₀, V₁` are columnWise codewords
- `R_star` is the set where affine combinations `Uᵣ` are close to `C^m`.
- `D` is the set of columns where `U₀` differs from `V₀` OR `U₁` differs from `V₁`.
- `R_star_star` is the set of pairs `(r, j)` where `r ∈ R_star` and column `j` of `Uᵣ`
equals column `j` of `Vᵣ` (set of `agreeing linearComb columns`)
Statement: The number of agreeing column pairs `(r, j)` is bounded by the number
of parameters in `R_star` times the number of columns *outside* `D`, plus the
number of columns *inside* `D`.
`|R**| ≤ |R*| * (n - |D|) + |D|`
-/
lemma R_star_star_upper_bound
    (U₀ U₁ : ι → (Fin m) → A)
    (hC_gap : ProximityGapAffineLines HLC e ε)
    (hR_star_card : (R_star HLC (m := m) (e := e) U₀ U₁).card > ε) :
      let ⟨V₀, V₁, _⟩ := constructInterleavedCodewordsAndRowWiseCA HLC U₀ U₁ hC_gap hR_star_card
      let D : Finset ι := disagreementSet U₀ U₁ V₀ V₁
      (R_star_star HLC (m := m) (e := e) U₀ U₁ V₀ V₁).card
        ≤ (R_star HLC (m := m) (e := e) U₀ U₁).card * (Fintype.card ι - D.card) + D.card
      := by
  classical -- Use classical logic for decidable predicates on filters

  -- 1. Define local variables
  let ⟨V₀, V₁, _⟩ := constructInterleavedCodewordsAndRowWiseCA HLC U₀ U₁ hC_gap hR_star_card
  let n := Fintype.card ι
  let R_s := R_star HLC (m := m) (e := e) U₀ U₁
  let D := disagreementSet U₀ U₁ V₀.val V₁.val
  set R_ss := R_star_star HLC (m := m) (e := e) U₀ U₁ V₀.val V₁.val
  set R_ss_in_D    := (R_star_star_filter_columns_in_D HLC U₀ U₁ V₀ V₁ e D)
  set R_ss_notin_D := (R_star_star_filter_columns_not_in_D HLC U₀ U₁ V₀ V₁ e D)

  -- 3. The card of R_ss is the sum of the cards of the disjoint partition.
  have h_card_split : R_ss.card = R_ss_notin_D.card + R_ss_in_D.card := by
    rw [← Finset.card_union_of_disjoint]
    congr
    · exact R_star_star_eq_union HLC U₀ U₁ V₀ V₁ e D
    · exact Disjoint.symm (disjoint_R_star_star_filter_columns_in_D_not_in_D HLC U₀ U₁ V₀ V₁ e D)

  simp only [ge_iff_le]
  -- 4. Apply the split
  rw [h_card_split]
  -- Goal: R_ss_notin_D.card + R_ss_in_D.card ≤ R_s.card * (n - D.card) + D.card

  -- 5. Apply the two new lemmas
  apply add_le_add
  · -- Prove R_ss_notin_D.card ≤ R_s.card * (n - D.card)
    have h_notin_D := card_agreeing_cells_notin_D HLC (m := m) (e := e) (U₀ := U₀) (U₁ := U₁)
      (V₀ := V₀) (V₁ := V₁) D (by rfl)
    exact Nat.le_of_eq h_notin_D
  · -- Prove R_ss_in_D.card ≤ D.card
    have h_in_D := card_agreeing_cells_in_D_le HLC (m := m) (e := e) (U₀ := U₀) (U₁ := U₁)
      (V₀ := V₀) (V₁ := V₁) D (by rfl)
    exact h_in_D

omit [Nonempty ι] [NoZeroDivisors F] [DecidableEq F] [Fintype A] [Module.Free F A] in
/-- **Lemma 3.4 (DG25): Lower Bound on R** Cardinality**
Context:
- Same as Lemma 3.2, including hypotheses on `C`, `e`, `V₀`, `V₁`, `R_star`.
- `R_star_star` is the set of pairs `(r, j)` where `r ∈ R_star` and column `j` of `Uᵣ`
equals column `j` of `Vᵣ`.
Statement: The number of agreeing column pairs `(r, j)` is at least the number
of parameters in `R_star` times the number of columns guaranteed to agree (`n - e`)
for each `r` (using Lemma 3.2), i.e. `|R**| ≥ (n - e) * |R*|`
-/
lemma R_star_star_lower_bound
    (U₀ U₁ : ι → (Fin m) → A)
    (he : e ∈ Finset.range (HLinearCode.uniqueDecodingRadius (HLC := HLC)))
    (hC_gap : ProximityGapAffineLines HLC e ε)
    (hR_star_card : (R_star HLC (m := m) (e := e) U₀ U₁).card > ε) :
      let ⟨V₀, V₁, _⟩ := constructInterleavedCodewordsAndRowWiseCA HLC U₀ U₁ hC_gap hR_star_card
      (R_star_star HLC (m := m) (e := e) U₀ U₁ V₀ V₁).card
        >= (Fintype.card ι - e) * (R_star HLC (m := m) (e := e) U₀ U₁).card
      := by
  classical
  /- DG25 Proof Sketch:
     Sum over r ∈ R*. For each such r:
     Apply Lemma 3.2 (using h_agree, he_udr, hR_star): Δ^m(Uᵣ, Vᵣ) ≤ e.
     By definition of Δ^m, this means Uᵣ and Vᵣ agree on ≥ n - e columns j.
     So, row r contributes ≥ n - e to |R**|.
     Summing gives |R**| ≥ |R*| * (n - e).
  -/
  -- 1. Define local variables
  let V₀ := (constructInterleavedCodewordsAndRowWiseCA HLC U₀ U₁ hC_gap hR_star_card).1
  let V₁ := (constructInterleavedCodewordsAndRowWiseCA HLC U₀ U₁ hC_gap hR_star_card).2.1
  let n := Fintype.card ι
  let R_s := R_star HLC (m := m) (e := e) U₀ U₁
  let R_ss := R_star_star HLC (m := m) (e := e) U₀ U₁ V₀.val V₁.val

  simp only [ge_iff_le]
  simp only [R_star_star]
  rw [Finset.card_filter]
  rw [Finset.sum_product]

  have h_card_ge_per_r: ∀ r : R_star HLC (e := e) U₀ U₁, (Fintype.card ι - e) ≤ (∑ j, if
      affineLineEvaluation (F := F) U₀ U₁ (r, j).1 (r, j).2
      = affineLineEvaluation (F := F) ↑V₀ ↑V₁ (r, j).1 (r, j).2 then 1 else 0) := by
    intro r
      -- Let Uᵣ and Vᵣ be the affine points for this r
    let Uᵣ := affineLineEvaluation (F := F) U₀ U₁ r
    let Vᵣ := affineLineEvaluation (F := F) V₀.val V₁.val r

    -- The sum is the number of agreeing columns, which is `n - hammingDist(Uᵣ, Vᵣ)`
    have h_sum_eq_agreeing_cols :
        (∑ j, if Uᵣ j = Vᵣ j then 1 else 0) = n - Δ₀(Uᵣ, Vᵣ) := by
      -- 1. `∑ j, if P j then 1 else 0` is the definition of `(Finset.filter P Finset.univ).card`
      rw [Finset.sum_boole]

      -- 2. Unfold the notation
      -- `n` is `(Finset.univ : Finset ι).card`
      dsimp only [Nat.cast_id, n]
      rw [←Finset.card_univ]
      -- `Δ₀(Uᵣ, Vᵣ)` is `hammingDist Uᵣ Vᵣ`
      unfold hammingDist
      apply Nat.eq_sub_of_add_eq
      rw [Finset.card_filter, Finset.card_filter]

      change ((∑ i, if Uᵣ i = Vᵣ i then 1 else 0) + ∑ i, if Uᵣ i ≠ Vᵣ i then 1 else 0) = #univ
      rw [← Finset.sum_add_distrib]
      simp_rw [ne_eq]
      -- simp will solve the `ite` logic and apply `sum_const_one`
      simp only [ite_not, card_univ]
      have h_inner : ∀ x, ((if Uᵣ x = Vᵣ x then 1 else 0) + if Uᵣ x = Vᵣ x then 0 else 1) = 1
        := fun x => by
        by_cases h : Uᵣ x = Vᵣ x
        · simp only [h, if_true]
        · simp only [h, if_false]
      simp_rw [h_inner]
      simp only [sum_const, card_univ, smul_eq_mul, mul_one]
    rw [h_sum_eq_agreeing_cols]
    -- Goal: n - e ≤ n - hammingDist Uᵣ Vᵣ
    -- This is equivalent to `hammingDist Uᵣ Vᵣ ≤ e`
    -- We use `Nat.sub_le_sub_left_iff` which requires `hammingDist Uᵣ Vᵣ ≤ n`
    have h_dist_le_n : hammingDist Uᵣ Vᵣ ≤ e := by
    -- This is exactly the conclusion of Lemma 3.2 (affineWord_close_to_affineInterleavedCodeword)
      let res := affineWord_close_to_affineInterleavedCodeword (U₀ := U₀) (U₁ := U₁)
        (he := he) (hC_gap := hC_gap) (hR_star_card := hR_star_card) (r := r)
      simp only [Fin.isValue, eq_mpr_eq_cast, cast_eq, ENNReal.coe_natCast,
        Lean.Elab.WF.paramLet] at res
      exact res
    exact Nat.sub_le_sub_left h_dist_le_n (Fintype.card ι)

  have h_left : (Fintype.card ι - e) * #(R_star HLC (e := e) U₀ U₁)
    = ∑ r ∈ R_star HLC (e := e) U₀ U₁, (Fintype.card ι - e) := by
    rw [Finset.sum_const]
    simp only [smul_eq_mul]
    exact Nat.mul_comm (Fintype.card ι - e) #(R_star HLC U₀ U₁)
  rw [h_left]
  apply Finset.sum_le_sum
  intro r hr_mem
  exact h_card_ge_per_r (Subtype.mk r hr_mem)

omit [NoZeroDivisors F] [Module.Free F A] [Nontrivial ↥HLC] [Nonempty ι] [Fintype A]
  [DecidableEq A] [DecidableEq F] in
lemma probShadedAffineCombInterleavedCodeword_gt_threshold_iff
  (U₀ U₁ : ι → (Fin m) → A) :
  Pr_{ let r ←$ᵖ F }[
    Δ₀(affineLineEvaluation (F := F) U₀ U₁ r,
      HLC.toInterleavedCode (Fin m)) ≤ e ] > ((ε: ℝ≥0) / (Fintype.card F : ℝ≥0))
  ↔ (R_star HLC (m := m) (e := e) U₀ U₁).card > ε := by
  conv_lhs =>
    rw [prob_uniform_eq_card_filter_div_card]
    rw [gt_iff_lt]
    simp only [ENNReal.coe_natCast]
    simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
      ENNReal.natCast_ne_top, ENNReal.div_lt_div_iff_left (c := ((Fintype.card F) : ENNReal)),
      Nat.cast_lt]
    rw [←gt_iff_lt]
  rfl

/--
This lemma proves the final algebraic step in the DG25 Theorem 3.1 proof.
It shows that if `R > e + 1`, then `e * (R / (R - 1)) < e + 1`.

The intuition is that the fraction `R / (R - 1)` is always greater than 1,
but as `R` gets larger, it gets closer to 1. The hypothesis `R > e + 1`
provides a strong enough bound to ensure the product `e * (fraction)`
doesn't "overshoot" `e + 1`.
-/
lemma e_mul_R_div_R_sub_1_lt_e_add_1_real {e R : ℕ} (hR_gt_e_add_1 : e + 1 < R) :
    ((e : ℝ) * (R : ℝ)) / ((R : ℝ) - 1) < (e : ℝ) + 1 := by
  have hR_gt_one : R > 1 := by omega
  have hR_Real_gt_one : (R : ℝ) > 1 := by exact Nat.cast_gt_Real_one R hR_gt_one
  have h_R_gt_e_add_1_real : ((e + 1) : ℝ) < (R : ℝ) := by
    rw [←Nat.cast_add_one (n := e)]
    apply Nat.cast_lt (α := ℝ) (m := e + 1) (n := R).mpr hR_gt_e_add_1
  have h_denom_pos : (R : ℝ) - 1 > 0 := by
    -- `linarith` solves this from the hypothesis
    linarith [hR_Real_gt_one]
  -- 3. Use `div_lt_iff` to multiply the denominator across
  -- This is the `ℝ` lemma for `a / b < c ↔ a < c * b` (since `b > 0`)
  rw [div_lt_iff₀ (hc := h_denom_pos)]
  -- Goal: ⊢ ↑e * ↑R < (↑e + 1) * (↑R - 1)
  -- 4. THIS IS THE KEY STEP
  -- Don't use `rw`. `linarith` will:
  --   a) Expand the RHS to: `e*R - e + R - 1`
  --   b) See the goal: `e*R < e*R - e + R - 1`
  --   c) Cancel `e*R` from both sides: `0 < R - e - 1`
  --   d) Rearrange: `e + 1 < R`
  --   e) See this is exactly your hypothesis `h_R_gt_e_add_1_real`
  linarith [h_R_gt_e_add_1_real]

omit [Nonempty ι] [Fintype A] in
/- **Theorem 3.1**. If `C` features proximity gaps for affine lines with respect to the
proximity parameter `e ∈ {0, ..., ⌊(d-1)/2⌋}` and the false witness bound
`ε ≥ e+1`, then, for each `m > 1`, `C`'s interleaving `C^m` also does.
-/
theorem affine_gaps_lifted_to_interleaved_codes {m : ℕ} {ε : ℕ}
    {e : Finset.range (HLinearCode.uniqueDecodingRadius (HLC := HLC))}
     (hε : ε ≥ e + 1)
    (hProximityGapAffineLines : ProximityGapAffineLines (F := F) (HLC := HLC) (e := e) (ε := ε)) :
    ProximityGapAffineLines (F := F) (HLC := HLC.toInterleavedCode (Fin m)) (e := e) (ε := ε) where
  gap_property := by
    -- 1. Unfold the definition of ProximityGapAffineLines for the interleaved code C^m.
    -- We must show that for any two words U₀, U₁, if the set of "close" affine
    -- combinations (R*) is large, then U₀ and U₁ have correlated agreement with C^m.
    intro U₀ U₁ hR_prob_shaded_affine_comb_gt_threshold
    -- `⊢ HLinearCode.correlatedAgreement₂ U₀ U₁ ↑e, i.e. |D| ≤ e`

    -- 2. Assume the hypothesis: |R*| > ε
    let hR_star_card_gt_ε := probShadedAffineCombInterleavedCodeword_gt_threshold_iff HLC
      U₀ U₁ (ε := ε) (e := e).mp hR_prob_shaded_affine_comb_gt_threshold

    have hR_star_card_gt1 : (R_star HLC (m := m) (e := e) U₀ U₁).card > 1 := by
      omega  -- |R*| > ε ≥ e + 1 ≥ 1
    have hR_star_card_gt1_Real : ((R_star HLC (m := m) (e := e) U₀ U₁).card : ℝ) > 1 := by
      exact Nat.cast_gt_Real_one (R_star HLC (m := m) (e := e) U₀ U₁).card hR_star_card_gt1

    -- 3. Use the hypothesis on the base code C (hProximityGapAffineLines)
    -- and the fact that |R*| > ε to construct the candidate
    -- interleaved codewords V₀ and V₁ in C^m.
    set V := constructInterleavedCodewordsAndRowWiseCA HLC U₀ U₁
      hProximityGapAffineLines (hR_star_card_gt_ε)
    let V₀ := V.1; let V₁ := V.2.1; let h_row_agreement := V.2.2
    set D := disagreementSet U₀ U₁ V₀ V₁
    have h_D_card_le_n : D.card ≤ Fintype.card ι := by
      dsimp only [disagreementSet, ne_eq, D]
      let res := Finset.card_filter_le (s := Finset.univ (α := ι))
        (p := fun colIdx => ¬U₀ colIdx = V₀.val colIdx ∨ ¬U₁ colIdx = V₁.val colIdx)
      rw [Finset.card_univ] at res
      exact res

    have h_D_le_D_mul_R_star_card: D.card ≤ D.card * (R_star HLC (m := m) (e := e) U₀ U₁).card := by
      conv_lhs => rw [←Nat.mul_one D.card]
      apply Nat.mul_le_mul_left; exact Nat.one_le_of_lt hR_star_card_gt_ε

    -- `e · |R*| ≥ |D| · (|R*| - 1)
    have h_e_mul_Rstar_card_ge:
      e * (R_star HLC (m := m) (e := e) U₀ U₁).card
        ≥ D.card * (R_star HLC (m := m) (e := e) U₀ U₁).card - D.card := by
      -- This comes from lemma 3.3: |R**| ≤ |R*|(n - |D|) + |D|
      -- and lemma 3.4: |R**| ≥ (n - e)|R*|
      have h_lemma_3_3 := R_star_star_upper_bound (HLC := HLC) (ε := ε) (m := m) (e := e)
        U₀ U₁ hProximityGapAffineLines hR_star_card_gt_ε
      have h_lemma_3_4 := R_star_star_lower_bound (HLC := HLC) (ε := ε) (m := m) (e := e)
        U₀ U₁ (coe_mem e) hProximityGapAffineLines hR_star_card_gt_ε
      simp only [ge_iff_le] at h_lemma_3_3 h_lemma_3_4

      set n := Fintype.card ι
      -- So (n - e)|R*| ≤ |R**| ≤ |R*|(n - |D|) + |D|
      have h_le_trans := le_trans h_lemma_3_4 h_lemma_3_3
      -- ↔ n * |R*| - e * |R*| ≤ n * |R*| - |D| * |R*| + |D|
      rw [Nat.sub_mul (n := n) (m := e), Nat.mul_sub (n := (R_star HLC U₀ U₁).card),
        Nat.mul_comm (n := (R_star HLC U₀ U₁).card) (m := D.card)] at h_le_trans
      -- ↔ e * |R*| ≥ |D| * (|R*| - 1) (Q.E.D)
      have h_le_trans: n * #(R_star HLC (e := e) U₀ U₁) - e * #(R_star HLC (e := e) U₀ U₁)
        ≤ n * #(R_star HLC (e := e) U₀ U₁) - #D * #(R_star HLC (e := e) U₀ U₁) + #D := by
        conv_rhs => rw [Nat.mul_comm n (#(R_star HLC (e := e) U₀ U₁))]
        exact h_le_trans
      -- conv_rhs at h_le_trans => enter [2]; rw [←Nat.mul_one #D]
      rw [Nat.sub_add_eq_sub_sub_rev (a := n * #(R_star HLC U₀ U₁))
        (b :=  #D * #(R_star HLC U₀ U₁)) (c := #D) (h1 := h_D_le_D_mul_R_star_card)
        (h2 := Nat.mul_le_mul_right (#(R_star HLC U₀ U₁)) h_D_card_le_n)] at h_le_trans
      have h_le: #D * #(R_star HLC (e := e) U₀ U₁) - #D ≤ n * #(R_star HLC (e := e) U₀ U₁) := by
        apply Nat.sub_le_of_le_add; apply le_add_of_le_left;
        exact
          Nat.mul_le_mul_right (#(R_star HLC U₀ U₁)) h_D_card_le_n
      rw [Nat.sub_le_sub_iff_left (k := n * #(R_star HLC U₀ U₁)) (h := h_le)] at h_le_trans
      exact h_le_trans

    have h_e_mul_Rstar_card_ge_Real: (e : ℝ) * (R_star HLC (m := m) (e := e) U₀ U₁).card
      ≥ D.card * (R_star HLC (m := m) (e := e) U₀ U₁).card - D.card := by
      rw [←Nat.cast_mul, ←Nat.cast_mul, ←Nat.cast_sub (h := h_D_le_D_mul_R_star_card)]
      rw [ge_iff_le]
      rw [Nat.cast_le]
      exact h_e_mul_Rstar_card_ge

    -- `|D| ≤ e * (|R*| / (|R*| - 1))
    have h_D_card_le_e_mul_R_div_R_succ: D.card ≤ e *
      ((R_star HLC (m := m) (e := e) U₀ U₁).card : ℝ) /
      ((R_star HLC (m := m) (e := e) U₀ U₁).card - 1) := by
      rw [le_div_iff₀ (hc := by rw [sub_pos]; exact hR_star_card_gt1_Real)]
      rw [mul_sub, mul_one]
      exact h_e_mul_Rstar_card_ge_Real

    -- e * (|R*| / (|R*| - 1)) < e + 1 ↔ e * |R*| < e * |R*| - (e + 1) + |R*|
      -- ↔ 0 < |R*| - (e + 1) ↔ e + 1 < |R*|
    have h_e_mul_R_div_R_succ_lt: e * ((R_star HLC (m := m) (e := e) U₀ U₁).card : ℝ)
      / ((R_star HLC (m := m) (e := e) U₀ U₁).card - 1) < e + 1 := by
      exact e_mul_R_div_R_sub_1_lt_e_add_1_real (e := e) (R := (R_star HLC (m := m)
        (e := e) U₀ U₁).card) (hR_gt_e_add_1 := by omega)

    have h_D_card_le_e: D.card ≤ e := by
      apply Nat.le_of_lt_succ;
      have res := lt_of_le_of_lt (a := (#D : ℝ))
        (b := e * ((R_star HLC (m := m) (e := e) U₀ U₁).card : ℝ)
          / ((R_star HLC (m := m) (e := e) U₀ U₁).card - 1)) (c := (e + 1 : ℝ))
        (hab := h_D_card_le_e_mul_R_div_R_succ)
        (hbc := h_e_mul_R_div_R_succ_lt)
      rw [←Nat.cast_add_one, Nat.cast_lt] at res
      exact res

    dsimp only [D] at h_D_card_le_e
    exact (D_card_le_e_implies_interleaved_correlatedAgreement₂ (HLC := HLC)
      (m := m) (e := e) (ε := ε) U₀ U₁ hProximityGapAffineLines hR_star_card_gt_ε) (h_D_card_le_e)

/-- For each `r_{ϑ-1} ∈ 𝔽_q`, we abbreviate:
`p(r_{ϑ-1}) := Pr_{(r_0, ..., r_{ϑ-2}) ∈ 𝔽_q^{ϑ-1}} [`
  `d([⊗_{i=0}^{ϑ-2}(1-r_i, r_i)] · [(1-r_{ϑ-1}) · U₀ + r_{ϑ-1} · U₁], C) ≤ e]`
We define `R* := {r_{ϑ-1} ∈ 𝔽_q | p(r_{ϑ-1}) > (ϑ-1) · ε/q}`. We note that
`R*` is precisely the set of parameters `r_{ϑ-1} ∈ 𝔽_q` for which the half-length
matrix `(1-r_{ϑ-1}) · U₀ + r_{ϑ-1} · U₁` fulfills the inductive hypothesis (that is,
the hypothesis of Definition 2.3, with respect to the smaller list size parameter) -/
def R_star_tensor_filter (U₀ U₁ : (Fin (2 ^ m)) → ι → A) (r_affine_combine : F) : Prop :=
  (Pr_{let r ← $ᵖ (Fin m → F)}[ -- This syntax only works with (A : Type 0)
    Δ₀(tensorCombine_affineLineEvaluation (U₀ := U₀) (U₁ := U₁)
      (r := r) (r_affine_combine := r_affine_combine), HLC) ≤ e
  ] > (m * ε: ℝ≥0) / (Fintype.card F : ℝ≥0))

open Classical in
def R_star_tensor (U₀ U₁ : (Fin (2 ^ m)) → ι → A) : Finset F :=
  Finset.filter (fun r_affine_combine : F =>
    R_star_tensor_filter HLC (m := m) (e := e) (ε := ε) U₀ U₁ r_affine_combine
  ) Finset.univ

omit [Nonempty ι] [NoZeroDivisors F] [DecidableEq F] [Fintype A]
  [Module.Free F A] [Nontrivial ↥HLC] in
open Classical in
/-- inductively to each such matrix, we conclude that,
for each `r_{ϑ-1} ∈ R*`, `d^{2^{ϑ-1}}((1-r_{ϑ-1}) · U₀ + r_{ϑ-1} · U₁, C^{2^{ϑ-1}}) ≤ e`
-/
lemma correlatedAgreement_of_mem_R_star_tensor
    {ϑ_pred : ℕ}
    (ih : ∀ u_prev, tensorStyleProximityGap HLC e ε ϑ_pred u_prev)
    (u : Fin (2 ^ (ϑ_pred + 1)) → (ι → A)) :
    -- This hypothesis comes from the main theorem's inductive step
    let ⟨U₀, U₁⟩ := splitHalfRowWiseInterleavedWords (ϑ := ϑ_pred) u
    ∀ (r : R_star_tensor HLC (e := e) (ε := ε) U₀ U₁),
    HLC.correlatedAgreement (affineLineEvaluation U₀ U₁ r.val) e := by
  -- simp only [Nat.add_one_sub_one, Subtype.forall]
  intro r
  apply ih
  -- ⊢ Pr_{ r ← Fin (ϑ_pred) → F}[ Δ₀(tensorCombine Uᵣ (r := r), HLC) ≤ e ] > (ϑ_pred * ε) / |𝔽|
  -- i.e. these r must satisfy (tensor-folding with the affine random combination)
    -- must be close to individual-row code HLC
  set U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ_pred) u).1
  set U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ_pred) u).2

  unfold R_star_tensor at r
  -- Now, just state that the proof is `r.property`
  have hr:  R_star_tensor_filter HLC U₀ U₁ ↑r :=
    (Finset.mem_filter (s := Finset.univ (α := F)) (a := r)
      (p := R_star_tensor_filter HLC (e := e) (ε := ε) U₀ U₁).mp (coe_mem r)).2
  unfold R_star_tensor_filter at hr
  exact hr

def tensorCombine_affineComb_split_last_close {ϑ : ℕ}
  (u : Fin (2 ^ (ϑ + 1)) → (ι → A)) (e : ℕ) (r_last : F) (r_init : Fin (ϑ) → F) : Prop :=
    let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
    let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
    Δ₀(tensorCombine (affineLineEvaluation U₀ U₁ r_last) r_init, ↑HLC) ≤ (e : ℕ∞)

omit [Nonempty ι] [NoZeroDivisors F] [Fintype A] [Module.Free F A] [Nontrivial ↥HLC] in
open Classical in
lemma prob_R_star_gt_threshold
  {ϑ : ℕ}
  (u : Fin (2 ^ (ϑ + 1)) → (ι → A)) (e : ℕ)
  (hP_tensorCombine_affine_close_gt :
    Pr_{ let r_last ← $ᵖ F; let r_init ← $ᵖ (Fin (ϑ) → F)}[tensorCombine_affineComb_split_last_close
      (HLC := HLC) (u := u) (e := e) r_last r_init]
    > (((Nat.cast (R := ℝ≥0) (ϑ + 1)) * ε : ℝ≥0) / ((Fintype.card F : ℝ≥0) : ℝ≥0))) :
    let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
    let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
    let R_star_set := R_star_tensor HLC (e := e) (ε := ε) U₀ U₁
  Pr_{ let r ← $ᵖ F }[ r ∈ R_star_set ] > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
  -- 1. Setup abbreviations for clarity
  set U₀ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).1
  set U₁ := (splitHalfRowWiseInterleavedWords (ϑ := ϑ) u).2
  set R_star_set := R_star_tensor HLC (m := ϑ) (e := e) (ε := ε) U₀ U₁

  let q := (Fintype.card F : ENNReal)
  let ε_enn := (ε : ENNReal)
  let ϑ_enn := (ϑ : ENNReal)
  have hq_ne_zero : q ≠ 0 := Ne.symm (NeZero.ne' q)
  --  ENNReal.natCast_ne_zero.mpr Fintype.card_ne_zero
  have hq_ne_top : q ≠ ⊤ := ENNReal.natCast_ne_top (Fintype.card F)
  have h_finite : (↑(Nat.cast (R := ℝ≥0) ϑ) * ↑ε / q) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top (ENNReal.coe_ne_top) ENNReal.coe_ne_top)
      (Ne.symm (NeZero.ne' q))

  -- Define the thresholds from the paper
  let cur_false_witness_threshold := (((Nat.cast (R := ℝ≥0) (ϑ+1)) * ε: ℝ≥0) : ENNReal) / q
  let prev_false_witness_threshold := (((Nat.cast (R := ℝ≥0) ϑ) * ε: ℝ≥0) : ENNReal) / q
  let goal_threshold := (ε_enn / q)

  -- 2. Define the combined distribution and the two predicates
  let D : PMF (F × (Fin (ϑ) → F)) := do
    let r_last ← $ᵖ F
    let r_init ← $ᵖ (Fin (ϑ) → F)
    pure (r_last, r_init)
  set f := fun (r : F × (Fin ϑ → F)) =>
    tensorCombine_affineComb_split_last_close (HLC := HLC) (u := u) (e := e) r.1 r.2
  set g := fun (r : F × (Fin ϑ → F)) => r.1 ∈ R_star_set

  -- 3. Rewrite the hypothesis `hP...` using the combined distribution `D`
  have h_D_eq_prod : D = $ᵖ (F × (Fin ϑ → F)) := by
    rw [←do_two_uniform_sampling_eq_uniform_prod]
  rw [Pr_multi_let_equiv_single_let] at hP_tensorCombine_affine_close_gt

  -- `hP_f_gt` is the hypothesis `Pr[f] > cur_false_witness_threshold`
  have h_P_f_gt : Pr_{let r ← D}[f r] > cur_false_witness_threshold := by
    exact hP_tensorCombine_affine_close_gt

  -- 4. Apply the Law of Total Probability: Pr[f] = Pr[f ∧ g] + Pr[f ∧ ¬g]
  have h_split : Pr_{let r ← D}[f r] =
    Pr_{let r ← D}[g r ∧ f r] + Pr_{let r ← D}[¬(g r) ∧ f r] := by
    apply Pr_add_split_by_complement

  -- 5. Bound the two terms on the RHS
  -- 5a. Pr[f ∧ g] ≤ Pr[g]
  have h_Pr_f_and_g_le_Pr_g : Pr_{let r ← D}[g r ∧ f r] ≤ Pr_{let r ← D}[g r] := by
    apply Pr_le_Pr_of_implies
    intro r h_imp; exact h_imp.1

  -- 5b. Pr[f ∧ ¬g] ≤ prev_false_witness_threshold (i.e., ϑε/q) (This is the "false positive" bound)
  -- Proof sketch: Pr_{let r ← D}[¬(g r) ∧ f r]
    -- = (1/q) * ∑' r_last, Pr_{r_init}[ r_last ∉ R_star_set ∧ f (r_init||r_last)]
  -- (1/q) * ∑' r_last, (if r_last ∉ R* then Pr_{r_init}[f(r_last, r_init)] else 0)
  -- ≤ (1/q) * ∑' r_last, (if r_last ∉ R* then (ϑ * ε/q) else 0)
  -- ≤ (1/q) * ∑' r_last, (ϑ * ε/q) = (1/q) * (ϑ * ε/q * q) = ϑ*ε/q (Q.E.D)
  have h_bound_not_g : Pr_{let r ← D}[¬(g r) ∧ f r] ≤ prev_false_witness_threshold := by
    dsimp only [D]
    rw [do_two_uniform_sampling_eq_uniform_prod (α := F) (β := (Fin ϑ → F))]
    rw [prob_split_uniform_sampling_of_prod]
    -- ⊢ Pr_{ x ← $ᵖ F; y ← $ᵖ (Fin ϑ → F)}[¬g (x, y) ∧ f (x, y)] ≤ prev_false_witness_threshold
    rw [prob_tsum_form_split_first (D := $ᵖ F) (D_rest :=
      fun r_last => (do let r_init ← $ᵖ (Fin ϑ → F); pure (¬(r_last ∈ R_star_set)
        ∧ f (r_last, r_init))))]
    conv_lhs =>
      simp only [PMF.uniformOfFintype_apply]; rw [ENNReal.tsum_mul_left]
      simp only [prob_const_and_prop_eq_ite]
    -- (1/q) * ∑' r_last, (if r_last ∉ R* then Pr_{r_init}[f(r_last, r_init)] else 0)
    have h_inner_le : ∀ (i: F), (if i ∉ R_star_set then
      Pr_{let r_init ← $ᵖ (Fin ϑ → F)}[f (i, r_init)] else 0)
        ≤ prev_false_witness_threshold := fun i => by
      by_cases hi_mem: i ∈ R_star_set
      · simp only [hi_mem, not_true_eq_false, ↓reduceIte, zero_le]
      · simp only [hi_mem, not_false_eq_true, ↓reduceIte]
        have h_i_mem_iff := Finset.mem_filter (s := Finset.univ (α := F)) (a := i)
          (p := fun r_last => R_star_tensor_filter HLC (e := e) (ε := ε) U₀ U₁ r_last
      )
        simp only [R_star_set] at hi_mem
        have h_i_ne_mem_and_close := (Iff.not h_i_mem_iff).mp hi_mem
        have h_i_mem_univ: i ∈ Finset.univ (α := F) := by
          simp only [mem_univ]
        simp only [h_i_mem_univ, true_and] at h_i_ne_mem_and_close
        unfold R_star_tensor_filter at h_i_ne_mem_and_close
        simp only [gt_iff_lt, not_lt] at h_i_ne_mem_and_close
        exact h_i_ne_mem_and_close

    calc
      _ ≤ (((Fintype.card F): ENNReal)⁻¹ * ∑' (i : F), prev_false_witness_threshold) := by
        apply ENNReal.mul_le_mul_left (h0 := ENNReal.inv_ne_zero.mpr hq_ne_top)
          (hinf := ENNReal.inv_ne_top.mpr hq_ne_zero).mpr
        apply ENNReal.tsum_le_tsum h_inner_le
      _ ≤ _ := by
        simp only [ENNReal.tsum_const, ENat.card_eq_coe_fintype_card, ENat.toENNReal_coe]
        rw [←mul_assoc]
        simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
          ENNReal.natCast_ne_top, ENNReal.inv_mul_cancel, one_mul, le_refl]

  -- 6. Chain the inequalities: `(ϑ+1)ε/q < Pr[f] ≤ Pr[g] + Pr[f ∧ ¬g] ≤ Pr[g] + ϑε/q`
  have h_total_lt_Pr_g_add_term : cur_false_witness_threshold
    < Pr_{let r ← D}[g r] + prev_false_witness_threshold := by
    calc cur_false_witness_threshold
      < Pr_{let r ← D}[f r] := h_P_f_gt
      _ = Pr_{let r ← D}[g r ∧ f r] + Pr_{let r ← D}[¬(g r) ∧ f r] := by rw [h_split]
      _ ≤ Pr_{let r ← D}[g r] + Pr_{let r ← D}[¬(g r) ∧ f r] :=
        add_le_add_right h_Pr_f_and_g_le_Pr_g _
      _ ≤ Pr_{let r ← D}[g r] + prev_false_witness_threshold := add_le_add_left h_bound_not_g _
      _ ≤ _ := by simp only [bind_pure_comp, le_refl]

  -- 7. Prove Pr[g] is equal to the goal probability (marginalization)
  have h_Pr_g_eq : Pr_{let r ← D}[g r] = Pr_{let r ← $ᵖ F}[ r ∈ R_star_set ] := by
    have h_D_rw : D = (do { let x ← $ᵖ F; let y ← $ᵖ (Fin ϑ → F); pure (x, y)}) := rfl
    rw [h_D_rw]
    rw [do_two_uniform_sampling_eq_uniform_prod]
    rw [prob_marginalization_first_of_prod]

  -- 8. Rearrange to get the final result
  -- We have: cur_false_witness_threshold < Pr[g] + prev_false_witness_threshold
  -- We want: goal_threshold < Pr[g]
  -- This is: cur_false_witness_threshold - prev_false_witness_threshold < Pr[g]
  rw [h_Pr_g_eq] at h_total_lt_Pr_g_add_term
  have h_lt_sub : cur_false_witness_threshold - prev_false_witness_threshold
    < Pr_{let r ← $ᵖ F}[r ∈ R_star_set] := by
    rw [ENNReal.sub_lt_iff_lt_right]
    · omega
    · exact h_finite
    · dsimp only [ENNReal.coe_mul, ENNReal.coe_natCast, prev_false_witness_threshold,
      cur_false_witness_threshold]
      apply ENNReal.div_le_div
      · by_cases h_ε_ne_zero : ε ≠ 0
        · let mul_right_le:= (ENNReal.mul_le_mul_right (a := ϑ) (b := Nat.cast (R := ENNReal)
            (ϑ + 1)) (c := ε) (Nat.cast_ne_zero.mpr h_ε_ne_zero) (ENNReal.natCast_ne_top ε)).mpr
          apply mul_right_le
          simp only [Nat.cast_add, Nat.cast_one, self_le_add_right]
        · have h_ε_eq_zero : ε = 0 := by omega
          rw [h_ε_eq_zero]; simp only [CharP.cast_eq_zero, mul_zero, Nat.cast_add, Nat.cast_one,
            le_refl]
      · exact Preorder.le_refl q

  have h_sub_eq_goal : cur_false_witness_threshold - prev_false_witness_threshold
    = goal_threshold := by
    unfold cur_false_witness_threshold prev_false_witness_threshold goal_threshold
    simp only [Nat.cast_add, Nat.cast_one, ENNReal.coe_add, ENNReal.coe_one,
      ENNReal.coe_mul, ENNReal.coe_natCast, ε_enn]
    rw [add_mul]
    simp only [one_mul]
    rw [ENNReal.add_div]
    rw [add_comm, ENNReal.add_sub_cancel_right]
    omega

  rw [h_sub_eq_goal] at h_lt_sub
  exact h_lt_sub

omit [Nonempty ι] [NoZeroDivisors F] [Fintype A] [Module.Free F A] [Nontrivial ↥HLC] in
/- **Theorem 3.6 (Angeris-Evans-Roh AER24): Interleaved Affine Gaps -> Tensor Gaps**
If, for **every** interleaving factor `m ≥ 1`, the `m`-fold interleaved code `C^m`
features proximity gaps for affine lines with respect to parameters `e` and `ε`,
then the original code `C` also features tensor-style proximity gaps with respect
to the same parameters `e` and `ε`.
-/
theorem interleaved_affine_gaps_imply_tensor_gaps
    (hC_proximityGapAffineLines : ProximityGapAffineLines (F := F) (HLC := HLC) (e := e) (ε := ε))
    (h_interleaved_gaps : ∀ m : ℕ, m ≥ 1 →
      ProximityGapAffineLines (F := F) (HLC.toInterleavedCode (Fin m)) e ε) :
    TensorStyleProximityGaps (F := F) HLC e ε where
  gap_property := by
    intro ϑ
    induction ϑ with
    | zero =>
      intro u
      simp only [gt_iff_lt, lt_self_iff_false, IsEmpty.forall_iff]
    | succ ϑ_sub_1 ih =>
      cases ϑ_sub_1 with
      | zero =>
        -- `ϑ = 1`
        simp only [Nat.reduceAdd, Nat.reducePow, zero_add, gt_iff_lt, zero_lt_one, forall_const]
        intro u
        let toAffineLineEval := tensorCombine₁_eq_affineLineEvaluation (F := F) (u := u)
        intro hprob_gt
        simp_rw [toAffineLineEval] at hprob_gt
        let prob_eq := prob_uniform_singleton_finFun_eq (F := F)
          (P := fun r => Δ₀(affineLineEvaluation (u 0) (u 1) r, HLC) ≤ e)
        -- Convert sampling (r ← (Fin 1 → F)) into sampling (r ← F)
        simp_rw [prob_eq, Nat.cast_one, one_mul] at hprob_gt
        have h_correlated_agreement := hC_proximityGapAffineLines.gap_property (u 0) (u 1) hprob_gt
        simp only [HLinearCode.correlatedAgreement₂, Fin.isValue] at h_correlated_agreement
        have h_u_eq: u = finMapTwoWords (u 0) (u 1) := by
          funext rowIdx
          match rowIdx with
          | 0 => rfl
          | 1 => rfl
        rw [h_u_eq.symm] at h_correlated_agreement
        exact h_correlated_agreement
      | succ ϑ_sub_2 =>
        intro u hu
        -- `ϑ ≥ 2`
        -- set ϑ_sub_1 := ϑ_sub_2 + 1
        let ϑ := ϑ_sub_2 + 1 + 1
        have hϑ : ϑ = ϑ_sub_2 + 1 + 1 := by rfl
        -- have hfinϑ : Fin ϑ = Fin (ϑ_sub_2 + 1 + 1) := by rfl
        set U₀ : Fin (2 ^ (ϑ_sub_2 + 1)) → ι → A :=
          (splitHalfRowWiseInterleavedWords (ϑ := ϑ_sub_2 + 1) u).1
        set U₁ : Fin (2 ^ (ϑ_sub_2 + 1)) → ι → A :=
          (splitHalfRowWiseInterleavedWords (ϑ := ϑ_sub_2 + 1) u).2
        intro hP_tensorCombine_close_gt

        have h_finsnoc_eq_r: ∀ r: Fin (ϑ_sub_2 + 1 + 1) → F,
          Fin.snoc (fun (i : Fin (ϑ_sub_2 + 1)) ↦ r i.castSucc)
            (r (Fin.last (ϑ_sub_2 + 1))) = r := fun r => by
          funext i
          have hi_le_lt := i.isLt
          by_cases h : i = Fin.last (ϑ_sub_2 + 1)
          · simp only [h, Fin.snoc_last]
          · have h_i_ne_last: i ≠ Fin.last (ϑ_sub_2 + 1) := by omega
            have h_i_ne_last_val: i.val ≠ Fin.last (ϑ_sub_2 + 1) := by omega
            rw [Fin.val_last] at h_i_ne_last_val
            have h_i_lt: i.val < (ϑ_sub_2 + 1) := by omega
            simp only [Fin.snoc, Fin.castSucc_castLT, cast_eq, dite_eq_ite, ite_eq_left_iff, not_lt]
            simp only [isEmpty_Prop, not_le, h_i_lt, IsEmpty.forall_iff]
        let P : F → (Fin (ϑ_sub_2 + 1) → F) → Prop := fun r_last r_init =>
          Δ₀(tensorCombine (u:=u) (r:=Fin.snoc r_init r_last), HLC) ≤ e

        let hP_split_r_last := prob_split_last_uniform_sampling_of_finFun
          (ϑ := ϑ_sub_2 + 1) (F := F) (P := P)
        unfold P at hP_split_r_last
        simp_rw [h_finsnoc_eq_r] at hP_split_r_last

        rw [hP_split_r_last] at hP_tensorCombine_close_gt

        -- Now we have two randomness sampling in hP_tensorCombine_close_gt :
        -- `((ϑ_sub_2 + 1 + 1) * ε) / |𝔽|
          -- < Pr_{ r_last; r_init }[  Δ₀((Fin.snoc r_init r_last)|⨂|u, ↑HLC) ≤ ↑e)) ]` (0)
        -- We need to achieve the upperbound for hP_tensorCombine_close_gt probability by showing:
        -- i.e. `Pr_{ r_last; r_init }[  Δ₀((Fin.snoc r_init r_last)|⨂|u, ↑HLC) ≤ ↑e)) ]`
        -- `= Pr_{ r_last; r_init }[ Δ₀((r_init)|⨂|affineCombine(U₀, U₁, r_last), ↑HLC) ≤ ↑e)) ]`
        -- `= PR_{ r_last }[ r_init; Δ₀((r_init)|⨂|affineCombine(U₀, U₁, r_last), ↑HLC) ≤ ↑e)) ]`
        -- Divide into two cases: r_last ∈ R* and r_last ∉ R*
        -- `= Pr_{ r_last }[ r_last ∈ R* ∧
          -- Pr_{ r_init }[ Δ₀((r_init)|⨂|affineCombine(U₀, U₁, r_last), ↑HLC) ≤ ↑e)) ]` (1)
        -- `+ Pr_{ r_last }[ r_last ∉ R* ∧
          -- Pr_{ r_init }[ Δ₀((r_init)|⨂|affineCombine(U₀, U₁, r_last), ↑HLC) ≤ ↑e)) ]` (2)
        -- `(1) = Pr_{ r_last }[ r_last ∈ R* ]` (3)
        -- `(2): ∀ r ∉ R*, it's trivial that the probability
          -- ≤ ((ϑ_sub_2 + 1) * ε) / |𝔽|, due to definition of membership of R*` (4)

        -- Combine (0), (3), (4): we have `Pr_{ r_last }[ r_last ∈ R* ] > ε/|𝔽|` (5)

        -- Applying `correlatedAgreement_of_mem_R_star_tensor` to (5), we get
          -- `Δ₀((r_last)|⨂|affineCombine(U₀, U₁, r_last), ↑HLC) ≤ ↑e)) ] > ε/|𝔽|` (6)
        -- This is premise for affineProxmityGaps of interleaved code (`h_interleaved_gaps`)
          -- for `m = 2^{ϑ_sub_2 + 1}`, which directly leads to Q.E.D.

        let  ϑ_pred := ϑ_sub_2 + 1
        have h_ϑ_pred : ϑ_pred = ϑ_sub_2 + 1 := by rfl
        have h_ϑ : ϑ = ϑ_pred + 1 := by rfl
        -- Step 1: Apply tensorCombine recursive form
        -- We need the lemma `tensorCombine u r = tensorCombine (affineLineEvaluation U₀ U₁ r_last)`
                                                    -- `r_init` where `r = Fin.snoc r_init r_last`
        have tensorCombine_snoc_eq_tensorCombine_affine (r_init : Fin ϑ_pred → F) (r_last : F) :
            tensorCombine u (Fin.snoc r_init r_last) =
            tensorCombine (affineLineEvaluation U₀ U₁ r_last) r_init := by
          rw [tensorCombine_recursive_form]
          simp only [Fin.snoc_last, Fin.init_snoc]
          rfl

        -- Rewrite the probability using this identity
        simp_rw [tensorCombine_snoc_eq_tensorCombine_affine] at hP_tensorCombine_close_gt
        -- hP_tensorCombine_close_gt now looks like:
        -- Pr_{ r_last ← $ᵖ F; r_init ← $ᵖ (Fin ϑ_pred → F) }[ Δ₀(tensorCombine
            -- (affineLineEvaluation U₀ U₁ r_last) r_init, ↑HLC) ≤ ↑e ] > ↑(↑ϑ * ↑ε) / q
        -- Step 2 & 3: Define R* and apply Law of Total Probability
        let R_star_set := R_star_tensor HLC (m:=ϑ_pred) (e:=e) (ε:=ε) U₀ U₁

        -- Step 5: Show Pr[R*] > ε / q
        have h_prob_Rstar_gt_eps_div_q : Pr_{ let r ← $ᵖ F }[ r ∈ R_star_set ]
          > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
          let res := prob_R_star_gt_threshold (HLC := HLC) (ε := ε) (ϑ := ϑ_sub_2 + 1) (u := u)
            (e := e) (hP_tensorCombine_close_gt)
          exact res
        -- Convert Pr_{}[] to cardinality
        have h_R_star_card_gt_eps : R_star_set.card > ε := by
          rw [prob_uniform_eq_card_filter_div_card] at h_prob_Rstar_gt_eps_div_q -- Needs NNReal
          simp only [ENNReal.coe_natCast] at h_prob_Rstar_gt_eps_div_q
          rw [gt_iff_lt] at h_prob_Rstar_gt_eps_div_q
          have h_cancel_q_denom := ENNReal.div_lt_div_iff_left
            (a := (ε : ENNReal))
            (b := (#(filter (fun r => r ∈ R_star_set) Finset.univ)))
            (c := (Fintype.card F : ENNReal)) (hc₀ := by simp only [ne_eq,
            Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true]) (hc := by simp only [ne_eq,
              ENNReal.natCast_ne_top, not_false_eq_true])

          rw [h_cancel_q_denom] at h_prob_Rstar_gt_eps_div_q
          simp only [filter_univ_mem, Nat.cast_lt] at h_prob_Rstar_gt_eps_div_q
          exact h_prob_Rstar_gt_eps_div_q

        -- Step 6: Apply Inductive Hypothesis for r_last ∈ R*
        have h_line_close_to_C_m : ∀ (r : R_star_set),
          HLC.correlatedAgreement (affineLineEvaluation U₀ U₁ r.val) e := by
          intro r_in_Rstar
          -- Use the lemma proven earlier
          apply correlatedAgreement_of_mem_R_star_tensor (ih := fun u_prev =>
            ih u_prev (by omega) ) (u := u)

        -- Step 7: Apply Affine Gap of Interleaved Code C^(m = 2^(ϑ_sub_2 + 1))
        have h_C_m_gap := h_interleaved_gaps (2^(ϑ_sub_2 + 1)) (Nat.one_le_two_pow)

        -- Need the hypothesis Pr[...] > ε/q for h_C_m_gap
        have h_prob_line_gt_eps_div_q :
          Pr_{ let r ← $ᵖ F }[
            Δ₀(affineLineEvaluation (⊛|U₀) (⊛|U₁) r,
            ((HLC.toInterleavedCode (Fin (2 ^ (ϑ_sub_2 + 1)))))) ≤ e
          ] > (↑ε : ENNReal) / (Fintype.card F : ENNReal) := by
            -- This is implied by h_prob_Rstar_gt_eps_div_q becuz R* is a subset of the success set
            apply lt_of_le_of_lt' _ h_prob_Rstar_gt_eps_div_q
            have h_r_implies: ∀ (r : F), r ∈ R_star_set → Δ₀(affineLineEvaluation (⊛|U₀) (⊛|U₁) r,
              ((HLC.toInterleavedCode (Fin (2 ^ (ϑ_sub_2 + 1)))))) ≤ e := by
              intro r hr_in_Rstar
              specialize h_line_close_to_C_m ⟨r, hr_in_Rstar⟩
              unfold HLinearCode.correlatedAgreement at h_line_close_to_C_m
              exact h_line_close_to_C_m
            let Pr_le := Pr_le_Pr_of_implies (D := $ᵖ F)
              (g := fun r => Δ₀(affineLineEvaluation (⊛|U₀) (⊛|U₁) r,
                ((HLC.toInterleavedCode (Fin (2 ^ (ϑ_sub_2 + 1)))))) ≤ e)
                (f := fun r => r ∈ R_star_set) (h_imp := h_r_implies)
            simp only at Pr_le
            exact Pr_le

        -- Apply the gap property of C^m
        have h_final_gap : (HLC.toInterleavedCode
          (Fin (2^(ϑ_sub_2 + 1)))).correlatedAgreement₂ (⊛|U₀) (⊛|U₁) e := by
          apply h_C_m_gap.gap_property (u₀ := (⊛|U₀)) (u₁ := (⊛|U₁)) (h_prob_line_gt_eps_div_q)

        apply CA_split_rowwise_implies_CA (u := u) (e := e)
        exact h_final_gap
end MainResults

section RSCode_Corollaries
variable {n k : ℕ} {A : Type} [NeZero n] [NeZero k] (hk : k ≤ n)
  {domain : (Fin n) ↪ A} [DecidableEq A] [Field A] [Fintype A]
  [Nontrivial (ReedSolomon.code domain k)]

/-
Theorem 2.2 (Ben-Sasson, et al. [Ben+23, Thm. 4.1]). For each `e ∈ {0, ..., ⌊(d-1)/2⌋}`,
`RS_{F, S}[k, n]` exhibits proximity gaps for affine lines with respect to the
proximity parameter `e` and the false witness bound `ε := n`.
-/
theorem ReedSolomon_ProximityGapAffineLines_UniqueDecoding
    {domain : ι ↪ A} {k : ℕ} (hk : k ≤ Fintype.card ι) :
    ∀ e ∈ Finset.range (HLinearCode.uniqueDecodingRadius (HLC := ReedSolomon.code domain k)),
      ProximityGapAffineLines (F := A) (HLC := ReedSolomon.code domain k)
        (e := e) (ε := Fintype.card ι) := by
  intro e he_unique_decoding_radius
  sorry

/-- Corollary 3.7: RS Codes have Tensor-Style Proximity Gaps (Unique Decoding)
Example 4.1 shows that ε=n is tight for RS codes (Ben+23 Thm 4.1 is sharp). -/
theorem reedSolomon_tensorStyleProximityGap {e : ℕ} (hk : k ≤ n)
    (he : e ∈ Finset.range (HLinearCode.uniqueDecodingRadius (HLC := ReedSolomon.code domain k))) :
    TensorStyleProximityGaps (F := A) (HLC := ReedSolomon.code domain k)
        (e := e) (ε := n) where
  gap_property := by
    intro ϑ u h_prob_tensor_gt
    set C_RS: HLinearCode (Fin n) A A := ReedSolomon.code domain k
    have h_dist_RS := ReedSolomonCode.dist (F := A) (ι := Fin n)
      (domain := domain) (k := k) (h := hk)
    -- 1. Apply ReedSolomon_ProximityGapAffineLines_UniqueDecoding (BCIKS20 Thm 4.1)
    have h_fincard_n : Fintype.card (Fin n) = n := by simp only [Fintype.card_fin]
    have h_affine_gap_base : ProximityGapAffineLines (F := A) (HLC := C_RS)
        (e := e) (ε := n) := by
      let res := ReedSolomon_ProximityGapAffineLines_UniqueDecoding (hk := by omega) e he
      rw [h_fincard_n] at res
      exact res
    -- 2. Check condition ε ≥ e + 1 for Theorem 3.1
    have h_eps_ge_e1 : n ≥ e + 1 := by
      simp only [mem_range, HLinearCode.uniqueDecodingRadius] at he
      rw [h_dist_RS] at he
      simp only [add_tsub_cancel_right] at he
      rw [ge_iff_le];
      apply Nat.le_of_lt_succ;
      have h_lt : e + 1 < (n - k) / 2 + 1 + 1 := by omega
      have h_le : (n - k) / 2 + 1 ≤ n := by
        exact Nat.sub_div_two_add_one_le n k hk
      omega
    -- 3. Apply Theorem 3.1 inductively (or just state it's needed for Thm 3.6)
    have h_affine_gap_interleaved : ∀ m, (hm: m ≥ 1) →
        letI : Nonempty (Fin m × (Fin n)) := by
          apply nonempty_prod.mpr
          constructor
          · exact Fin.pos_iff_nonempty.mp hm
          · exact instNonemptyOfInhabited
        ProximityGapAffineLines
          (HLC := C_RS.toInterleavedCode (Fin m))
          e (Fintype.card (Fin n)) := by
      intro m hm
      let res := affine_gaps_lifted_to_interleaved_codes (HLC := C_RS)
        (F := A) (A := A) (hε := h_eps_ge_e1) (e := ⟨e, by omega⟩)
        (m := m) (hProximityGapAffineLines := h_affine_gap_base)
      rw [h_fincard_n]
      exact res
    -- 4. Apply Theorem 3.6 (AER24)
    let RS_tensor_gap := interleaved_affine_gaps_imply_tensor_gaps
      (HLC := C_RS) (h_interleaved_gaps := by
      rw [h_fincard_n] at h_affine_gap_interleaved
      exact h_affine_gap_interleaved) h_affine_gap_base
    exact RS_tensor_gap.gap_property (ϑ := ϑ) u h_prob_tensor_gt

end RSCode_Corollaries
