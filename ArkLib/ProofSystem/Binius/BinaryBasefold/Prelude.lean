/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.FieldTheory.AdditiveNTT.AdditiveNTT
import ArkLib.Data.MvPolynomial.Multilinear
import ArkLib.Data.Vector.Basic
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound
import ArkLib.Data.Probability.Notation
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ProximityGap.DG25

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

/-
## Main definitions
- `qMap_total_fiber_repr_coeff` : the coefficients of the `k`-th `ϑ`-step fiber point of a
  point `y` in the `(i+ϑ)`-th domain.
- `qMap_total_fiber_basis_sum_repr` : sum reprensetation of the `k`-th `ϑ`-step fiber point of a
  point `y` in the `(i+ϑ)`-th domain, relies on `qMap_total_fiber_repr_coeff` for proof.
-/
section Preliminaries

/-- Hamming distance is non-increasing under inner composition with an injective function.
NOTE : we can prove strict equality given `g` being an equivalence instead of injection.
-/
theorem hammingDist_le_of_outer_comp_injective {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {β : ι₂ → Type*} [∀ i, DecidableEq (β i)] [DecidableEq ι₂]
    (x y : ∀ i, β i) (g : ι₁ → ι₂) (hg : Function.Injective g) :
    hammingDist (fun i => x (g i)) (fun i => y (g i)) ≤ hammingDist x y := by
  -- Let D₂ be the set of disagreeing indices for x and y.
  let D₂ := Finset.filter (fun i₂ => x i₂ ≠ y i₂) Finset.univ
  -- The Hamming distance of the composed functions is the card of the preimage of D₂.
  suffices (Finset.filter (fun i₁ => x (g i₁) ≠ y (g i₁)) Finset.univ).card ≤ D₂.card by
    unfold hammingDist; simp only [this, D₂]
  -- The cardinality of a preimage is at most the cardinalit
    --  of the original set for an injective function.
  -- ⊢ #{i₁ | x (g i₁) ≠ y (g i₁)} ≤ #D₂
   -- First, we state that the set on the left is the `preimage` of D₂ under g.
  have h_preimage : Finset.filter (fun i₁ => x (g i₁) ≠ y (g i₁)) Finset.univ
    = D₂.preimage g (by exact hg.injOn) := by
    -- Use `ext` to prove equality by showing the membership conditions are the same.
    ext i₁
    -- Now `simp` can easily unfold `mem_filter` and `mem_preimage` and see they are equivalent.
    simp only [ne_eq, mem_filter, mem_univ, true_and, mem_preimage, D₂]

  -- Now, rewrite the goal using `preimage`.
  rw [h_preimage]
  set D₁ := D₂.preimage g (by exact hg.injOn)
  -- ⊢ #D₁ ≤ #D₂
  -- Step 1 : The size of a set is at most the size of its image under an injective function.
  have h_card_le_image : D₁.card ≤ (D₁.image g).card := by
    -- This follows directly from the fact that `g` is injective on the set D₁.
    apply Finset.card_le_card_of_injOn (f := g)
    · -- Goal 1 : Prove that `g` maps `D₁` to `D₁.image g`. This is true by definition of image.
      have res := Set.mapsTo_image (f := g) (s := D₁)
      convert res
      simp only [coe_image]
      --  (D₁.image g : Set ι₂)
    · -- Goal 2 : Prove that `g` is injective on the set `D₁`.
      -- This is true because our main hypothesis `hg` states that `g` is injective everywhere.
      exact Function.Injective.injOn hg

  -- Step 2 : The image of the preimage of a set is always a subset of the original set.
  have h_image_subset : D₁.image g ⊆ D₂ := by
    simp [D₁, Finset.image_preimage]

  -- Step 3 : By combining these two facts, we get our result.
  -- |D₁| ≤ |image g(D₁)|  (from Step 1)
  -- and |image g(D₁)| ≤ |D₂| (since it's a subset)
  exact h_card_le_image.trans (Finset.card_le_card h_image_subset)

variable {L : Type*}

/-- Tensor product of challenge vectors : for a local fold length `n`,
`CTensor(n, r_0, ..., r_{n-1}) = ⨂_{j=0}^{n-1}(1-r_j, r_j)` -/
def challengeTensorExpansion [CommRing L] (n : ℕ) (r : Fin n → L) :
  Fin (2 ^ n) → L := multilinearWeight (F := L) (ϑ := n) (r := r)

lemma challengeTensorExpansion_one [CommRing L] (r : L) :
  challengeTensorExpansion 1 (r := fun _ => r) = ![1 - r, r] := by
  unfold challengeTensorExpansion multilinearWeight
  simp only [reducePow, univ_unique, Fin.default_eq_zero, Fin.isValue, Fin.val_eq_zero,
    testBit_zero, decide_eq_true_eq, prod_ite_irrel, prod_const, card_singleton, pow_one,
    succ_eq_add_one, reduceAdd]
  funext i
  by_cases hi_eq_0 : i = 0
  · simp only [hi_eq_0, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, zero_ne_one, ↓reduceIte,
    cons_val_zero]
  · have hi_eq_1 : i = 1 := by omega
    simp only [hi_eq_1, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ, ↓reduceIte, cons_val_one,
      cons_val_fin_one]

/-- **Challenge Tensor Expansion Matrix**
Constructs the block-diagonal matrix containing the challenge tensor expansion of
size `n`: `MatrixCTensor(n, r) = [ CTensor(n, r)   0    ]`
                                `[   0     CTensor(n, r) ]` ,
which is used for decomposing `CTensor(n+1, r)` into a vector-matrix multiplication form. -/
def challengeTensorExpansionMatrix [CommRing L] (n : ℕ) (r : Fin n → L) :
    Matrix (Fin 2) (Fin (2 ^ (n + 1))) L :=
  let C_n_finmap := challengeTensorExpansion n r
  let C_n : Matrix (Fin (1)) (Fin (2 ^ n)) L := Matrix.of (fun _rowIdx colIdx => C_n_finmap colIdx)
  -- Create the block diagonal matrix using 1-row matrices
  let emptyBlock : Matrix (Fin 1) (Fin (2 ^ n)) L := 0
  let block := Matrix.from4Blocks (C_n)      emptyBlock
                                 emptyBlock (C_n)
  Matrix.reindex (eₘ := finCongr (by omega)) (eₙ := finCongr (by omega)) block

/-- Challenge Tensor Expansion Matrix multiplication on top half returns M_top * v_top
Proof similar to blockDiagMatrix_mulVec_F₂_eq_Fin_merge_PO2.
-/
lemma challengeTensorExpansionMatrix_mulVec_F₂_eq_Fin_merge_PO2 [CommRing L] (n : ℕ)
    (r : Fin n → L) (v_top : Fin (2 ^ n) → L) (v_bot : Fin (2 ^ n) → L) :
    let C_n_finmap := challengeTensorExpansion (n := n) (r := r)
    let C_n : Matrix (Fin (1)) (Fin (2 ^ n)) L :=
      Matrix.of (fun _rowIdx colIdx => C_n_finmap colIdx)
    (mergeFinMap_PO2_left_right (L := L) (n := 0) (left := ((C_n *ᵥ v_top) : (Fin 1) → L))
      (right := ((C_n *ᵥ v_bot) : (Fin 1) → L)) : (Fin 2) → L)
    = (challengeTensorExpansionMatrix (n := n) (r := r)) *ᵥ
      mergeFinMap_PO2_left_right (n := n) (left := v_top) (right := v_bot) := by
  dsimp only [challengeTensorExpansionMatrix]
  conv_rhs =>
    -- Move reindexing from Matrix to Vector
    rw [Matrix.reindex_mulVec]
  funext k
  unfold mergeFinMap_PO2_left_right
  unfold Matrix.from4Blocks Fin.reindex Matrix.mulVec dotProduct
  -- Now unfold everything
  simp only [zero_apply, finCongr_symm, Function.comp_apply, finCongr_apply, dite_mul, zero_mul,
    sum_dite_irrel, Fin.coe_cast]
  simp_rw [Fin.sum_univ_add]
  simp_rw [←Finset.sum_add_distrib]
  simp only [reduceAdd, reducePow, pow_zero, lt_one_iff, Fin.val_eq_zero_iff, Fin.isValue,
    Nat.pow_zero, of_apply, dite_eq_ite, Fin.coe_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta,
    Fin.natAdd_eq_addNat, Fin.coe_addNat, add_lt_iff_neg_right, not_lt_zero', add_zero,
    add_tsub_cancel_right, zero_add]

/-- **Challenge Tensor Expansion Decomposition Lemma (Vector-Matrix multiplication form)**
Prove that `CTensor(n+1, r_0, ..., r_n) = [1-r_n, r_n] * MatrixCTensor(n, r_0, ..., r_{n-1})` -/
lemma challengeTensorExpansion_decompose_succ [CommRing L] (n : ℕ) (r : Fin (n + 1) → L) :
    challengeTensorExpansion (n + 1) (r := r) = ![1 - r (Fin.last n), r (Fin.last n)]
      ᵥ* (challengeTensorExpansionMatrix n (r := Fin.init r)) := by
  funext colIdx
  unfold challengeTensorExpansionMatrix challengeTensorExpansion
  simp only [succ_eq_add_one, reduceAdd, reindex_apply]
  simp only [vecMul_eq_sum, Finset.sum_apply, Pi.smul_apply, submatrix_apply, smul_eq_mul,
    Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one, cons_val_fin_one]
  dsimp only [finCongr_symm, finCongr_apply, Fin.cast_eq_self, Fin.isValue]
  unfold Matrix.from4Blocks
  by_cases h_colIdx_lt_2_pow_n : colIdx.val < 2 ^ n
  · simp only [reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, zero_lt_one, ↓reduceDIte,
    Fin.coe_cast, h_colIdx_lt_2_pow_n, Fin.zero_eta, of_apply, mod_succ, lt_self_iff_false,
    zero_apply, mul_zero, add_zero]
    rw [multilinearWeight_succ_lower_half (r := r) (i := colIdx)
      (h_lt := h_colIdx_lt_2_pow_n), mul_comm]
  · have h_ne_lt_2_pow_n : ¬(colIdx.val < 2 ^ n) := by exact h_colIdx_lt_2_pow_n
    simp only [reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, zero_lt_one, ↓reduceDIte,
      Fin.coe_cast, h_ne_lt_2_pow_n, zero_apply, mul_zero, mod_succ, lt_self_iff_false, tsub_self,
      Fin.zero_eta, of_apply, zero_add]
    let u : Fin (2 ^ n) := ⟨colIdx.val - (2 ^ n), by omega⟩
    have h_eq: colIdx.val = u.val + (2 ^ n) := by dsimp only [u]; omega
    rw [multilinearWeight_succ_upper_half (r := r) (i := colIdx) (j := u)
      (h_eq := h_eq), mul_comm]

variable {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ]
variable (𝓑 : Fin 2 ↪ L)

/-- Fixes the first `v` variables of a `ℓ`-variate multivariate polynomial.
`t` -> `H_i` derivation
-/
noncomputable def fixFirstVariablesOfMQP (v : Fin (ℓ + 1))
  (H : MvPolynomial (Fin ℓ) L) (challenges : Fin v → L) : MvPolynomial (Fin (ℓ - v)) L :=
  have h_l_eq : ℓ = (ℓ - v) + v := by rw [Nat.add_comm]; exact (Nat.add_sub_of_le v.is_le).symm
  -- Step 1 : Rename L[X Fin ℓ] to L[X (Fin (ℓ - v) ⊕ Fin v)]
  let finEquiv := finSumFinEquiv (m := ℓ - v) (n := v).symm
  let H_sum : L[X (Fin (ℓ - v) ⊕ Fin v)] := by
    apply MvPolynomial.rename (f := (finCongr h_l_eq).trans finEquiv) H
  -- Step 2 : Convert to (L[X Fin v])[X Fin (ℓ - v)] via sumAlgEquiv
  let H_forward : L[X Fin v][X Fin (ℓ - v)] := (sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) H_sum
  -- Step 3 : Evaluate the poly at the point challenges to get a final L[X Fin (ℓ - v)]
  let eval_map : L[X Fin ↑v] →+* L := (eval challenges : MvPolynomial (Fin v) L →+* L)
  MvPolynomial.map (f := eval_map) (σ := Fin (ℓ - v)) H_forward

omit [NeZero ℓ] in
/-- Auxiliary lemma for proving that the polynomial sent by the honest prover is of degree at most
`deg` -/
theorem fixFirstVariablesOfMQP_degreeLE {deg : ℕ} (v : Fin (ℓ + 1)) {challenges : Fin v → L}
    {poly : L[X Fin ℓ]} (hp : poly ∈ L⦃≤ deg⦄[X Fin ℓ]) :
    fixFirstVariablesOfMQP ℓ v poly challenges ∈ L⦃≤ deg⦄[X Fin (ℓ - v)] := by
  -- The goal is to prove the totalDegree of the result is ≤ deg.
  rw [MvPolynomial.mem_restrictDegree]
  unfold fixFirstVariablesOfMQP
  dsimp only
  intro term h_term_in_support i
  -- ⊢ term i ≤ deg
  have h_l_eq : ℓ = (ℓ - v) + v := (Nat.sub_add_cancel v.is_le).symm
  set finEquiv := finSumFinEquiv (m := ℓ - v) (n := v).symm
  set H_sum := MvPolynomial.rename (f := (finCongr h_l_eq).trans finEquiv) poly
  set H_grouped : L[X Fin ↑v][X Fin (ℓ - ↑v)] := (sumAlgEquiv L (Fin (ℓ - v)) (Fin v)) H_sum
  set eval_map : L[X Fin ↑v] →+* L := (eval challenges : MvPolynomial (Fin v) L →+* L)
  have h_Hgrouped_degreeLE : H_grouped ∈ (L[X Fin ↑v])⦃≤ deg⦄[X Fin (ℓ - ↑v)] := by
    sorry
  have h_mem_support_max_deg_LE := MvPolynomial.mem_restrictDegree (R := L[X Fin ↑v]) (n := deg)
    (σ := Fin (ℓ - ↑v)) (p := H_grouped).mp (h_Hgrouped_degreeLE)
  have h_term_in_Hgrouped_support : term ∈ H_grouped.support := by
    have h_support_map_subset : ((MvPolynomial.map eval_map) H_grouped).support
      ⊆ H_grouped.support := by apply MvPolynomial.support_map_subset
    exact (h_support_map_subset) h_term_in_support
  -- h_Hgrouped_degreeLE
  let res : term i ≤ deg := h_mem_support_max_deg_LE term h_term_in_Hgrouped_support i
  exact res

/- `H_i(X_i, ..., X_{ℓ-1})` -> `g_i(X)` derivation -/
noncomputable def getSumcheckRoundPoly (i : Fin ℓ) (h : ↥L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc)])
    : L⦃≤ 2⦄[X] := by
  have h_i_lt_ℓ : ℓ - ↑i.castSucc > 0 := by
    have hi := i.2
    exact Nat.zero_lt_sub_of_lt hi
  have h_count_eq : ℓ - ↑i.castSucc - 1 + 1 = ℓ - ↑i.castSucc := by
    omega
  let challenges : Fin 0 → L := fun (j : Fin 0) => j.elim0
  let curH_cast : L[X Fin ((ℓ - ↑i.castSucc - 1) + 1)] := by
    convert h.val
  let g := ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ↑i.castSucc - 1), curH_cast ⸨X ⦃0⦄, challenges, x⸩' (by omega)
  exact ⟨g, by
    have h_deg_le_2 : g ∈ L⦃≤ 2⦄[X] := by
      simp only [g]
      let hDegIn := Sumcheck.Spec.SingleRound.sumcheck_roundPoly_degreeLE
        (R := L) (D := 𝓑) (n := ℓ - ↑i.castSucc - 1) (deg := 2) (i := ⟨0, by omega⟩)
        (challenges := fun j => j.elim0) (poly := curH_cast)
      have h_in_degLE : curH_cast ∈ L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc - 1 + 1)] := by
        rw! (castMode := .all) [h_count_eq]
        dsimp only [Fin.coe_castSucc, eq_mpr_eq_cast, curH_cast]
        rw [eqRec_eq_cast, cast_cast, cast_eq]
        exact h.property
      let res := hDegIn h_in_degLE
      exact res
    rw [mem_degreeLE] at h_deg_le_2 ⊢
    exact h_deg_le_2
  ⟩

lemma getSumcheckRoundPoly_eval_eq (i : Fin ℓ) (h : ↥L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc)]) (r : L) :
    (getSumcheckRoundPoly ℓ 𝓑 i h).val.eval r =
    ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ↑i.castSucc - 1),
      MvPolynomial.eval (Fin.cons r x ∘ Fin.cast (by
        have hi := i.2
        have h_i_lt_ℓ : ℓ - ↑i.castSucc > 0 := Nat.zero_lt_sub_of_lt hi
        omega
      )) h.val := by
  -- The proof follows from distributing Polynomial.eval over the sum and using
  -- eval_eq_eval_mv_eval_finSuccEquivNth to relate the partial evaluation to full evaluation
  -- with Fin.insertNth 0 r = Fin.cons r
  sorry

lemma getSumcheckRoundPoly_sum_eq (i : Fin ℓ) (h : ↥L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc)]) :
    (getSumcheckRoundPoly ℓ 𝓑 i h).val.eval 0 + (getSumcheckRoundPoly ℓ 𝓑 i h).val.eval 1 =
    ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ↑i.castSucc), MvPolynomial.eval x h.val := by
  rw [getSumcheckRoundPoly_eval_eq, getSumcheckRoundPoly_eval_eq]
  -- Split the RHS sum over the first variable
  -- The RHS is ∑ x ∈ {0,1}^n, h(x)
  -- We can split this as ∑ x₀ ∈ {0,1}, ∑ x' ∈ {0,1}^{n-1}, h(cons x₀ x')
  -- Which equals ∑ x' ∈ {0,1}^{n-1}, h(cons 0 x') + ∑ x' ∈ {0,1}^{n-1}, h(cons 1 x')
  -- This proof requires a bijection between Fin (ℓ - i.castSucc)
    -- and Fin 1 ⊕ Fin (ℓ - i.castSucc - 1) and using Finset.sum_bij to split the sum.
  sorry

end Preliminaries

noncomputable section       -- expands with 𝔽q in front
variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}

section Essentials
-- In this section, we ue notation `ϑ` for the folding steps, along with `(hdiv : ϑ ∣ ℓ)`

/-- Oracle function type for round i.
f^(i) : S⁽ⁱ⁾ → L, where |S⁽ⁱ⁾| = 2^{ℓ + R - i} -/
abbrev OracleFunction (i : Fin (ℓ + 1)) : Type _ := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by
  exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by exact Fin.is_le i)
    (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L

omit [NeZero ℓ] in
lemma fin_ℓ_lt_ℓ_add_one (i : Fin ℓ) : i < ℓ + 1 :=
  Nat.lt_of_lt_of_le i.isLt (Nat.le_succ ℓ)

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_lt_ℓ_add_R (i : Fin ℓ)
    : i.val < ℓ + 𝓡 := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin ℓ)
    : i.val < r := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_add_one_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin (ℓ + 1))
    : i.val < r := by omega

omit [NeZero ℓ] in
lemma fin_ℓ_steps_lt_ℓ_add_one (i : Fin ℓ) (steps : ℕ)
    (h : i.val + steps ≤ ℓ) : i.val + steps < ℓ + 1 :=
  Nat.lt_of_le_of_lt h (Nat.lt_succ_self ℓ)

omit [NeZero ℓ] in
lemma fin_ℓ_steps_lt_ℓ_add_R (i : Fin ℓ) (steps : ℕ) (h : i.val + steps ≤ ℓ)
    : i.val + steps < ℓ + 𝓡 := by
  apply Nat.lt_add_of_pos_right_of_le; omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_steps_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin ℓ) (steps : ℕ)
    (h : i.val + steps ≤ ℓ) : i.val + steps < r := by
  apply Nat.lt_of_le_of_lt (n := i + steps) (k := r) (m := ℓ) (h₁ := h)
    (by exact lt_of_add_right_lt h_ℓ_add_R_rate)

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma ℓ_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
    : ℓ < r := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_r_succ_bound {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin r) (h_i : i + 1 < ℓ + 𝓡)
    : i + 1 < r := by omega

/-!
### The Fiber of the Quotient Map `qMap`

Utilities for constructing fibers and defining the fold operations used by Binary Basefold.
-/

def Fin2ToF2 (𝔽q : Type*) [Ring 𝔽q] (k : Fin 2) : 𝔽q :=
  if k = 0 then 0 else 1

/-! Standalone helper for the fiber coefficients used in `qMap_total_fiber`. -/
noncomputable def fiber_coeff
    (i : Fin r) (steps : ℕ)
    (j : Fin (ℓ + 𝓡 - i)) (elementIdx : Fin (2 ^ steps))
    (y_coeffs : Fin (ℓ + 𝓡 - (i + steps)) →₀ 𝔽q) : 𝔽q :=
  if hj : j.val < steps then
    if Nat.getBit (k := j) (n := elementIdx) = 0 then 0 else 1
  else y_coeffs ⟨j.val - steps, by -- ⊢ ↑j - steps < ℓ + 𝓡 - ↑⟨↑i + steps, ⋯⟩
    rw [←Nat.sub_sub]; -- ⊢ ↑j - steps < ℓ + 𝓡 - ↑i - steps
    apply Nat.sub_lt_sub_right;
    · exact Nat.le_of_not_lt hj
    · exact j.isLt⟩

/-- Get the full fiber list `(x₀, ..., x_{2 ^ steps-1})` which represents the
joined fiber `(q⁽ⁱ⁺steps⁻¹⁾ ∘ ⋯ ∘ q⁽ⁱ⁾)⁻¹({y}) ⊂ S⁽ⁱ⁾` over `y ∈ S^(i+steps)`,
in which the LSB repsents the FIRST qMap `q⁽ⁱ⁾`, and the MSB represents the LAST `q⁽ⁱ⁺steps⁻¹⁾`
-/
noncomputable def qMap_total_fiber
    -- S^i is source domain, S^{i + steps} is the target domain
      (i : Fin r) (steps : ℕ) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
        (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)) :
    Fin (2 ^ steps) → sDomain 𝔽q β h_ℓ_add_R_rate i :=
  if h_steps : steps = 0 then by
    -- Base case : 0 steps, the fiber is just the point y itself.
    subst h_steps
    simp only [add_zero, Fin.eta] at y
    exact fun _ => y
  else by
    -- fun (k : 𝔽q) =>
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i+steps,by omega⟩) (by omega)
    let y_coeffs : Fin (ℓ + 𝓡 - (↑i + steps)) →₀ 𝔽q := basis_y.repr y

    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
    exact fun elementIdx => by
      let x_coeffs : Fin (ℓ + 𝓡 - i) → 𝔽q := fun j =>
        if hj_lt_steps : j.val < steps then
          if Nat.getBit (k := j) (n := elementIdx) = 0 then (0 : 𝔽q)
          else (1 : 𝔽q)
        else
          y_coeffs ⟨j.val - steps, by
            rw [←Nat.sub_sub]; apply Nat.sub_lt_sub_right;
            · exact Nat.le_of_not_lt hj_lt_steps
            · exact j.isLt
          ⟩  -- Shift indices to match y's basis
      exact basis_x.repr.symm ((Finsupp.equivFunOnFinite).symm x_coeffs)

/- TODO : state that the fiber of y is the set of all 2 ^ steps points in the
larger domain S⁽ⁱ⁾ that get mapped to y by the series of quotient maps q⁽ⁱ⁾, ..., q⁽ⁱ⁺steps⁻¹⁾. -/

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **qMap_fiber coefficient extraction**.
The coefficients of `x = qMap_total_fiber(y, k)` with respect to `basis_x` are exactly
the function that puts binary coeffs corresponding to bits of `k` in
the first `steps` positions, and shifts `y`'s coefficients.
This is the multi-step counterpart of `qMap_fiber_repr_coeff`.
-/
lemma qMap_total_fiber_repr_coeff (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩))
    (k : Fin (2 ^ steps)) :
    let x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (y := y) k
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)
      (h_i := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
    let y_coeffs := basis_y.repr y
    ∀ j, -- j refers to bit index of the fiber point x
      ((sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (by simp only; omega)).repr x) j
      = fiber_coeff (i := i) (steps := steps) (j := j) (elementIdx := k)
        (y_coeffs := y_coeffs) := by
  unfold fiber_coeff
  simp only
  intro j
  -- have h_steps_ne_0 : steps ≠ 0 := by exact?
  by_cases h_steps_eq_0 : steps = 0
  · subst h_steps_eq_0
    simp only [qMap_total_fiber, ↓reduceDIte, Nat.add_zero, eq_mp_eq_cast, cast_eq, not_lt_zero',
      tsub_zero, Fin.eta]
  · simp only [qMap_total_fiber, h_steps_eq_0, ↓reduceDIte, Module.Basis.repr_symm_apply,
    Module.Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_toFun]

def pointToIterateQuotientIndex (i : Fin (ℓ + 1)) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)) : Fin (2 ^ steps) := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
    (by apply Nat.lt_add_of_pos_right_of_le; simp only; omega)
  let x_coeffs := basis_x.repr x
  let k_bits : Fin steps → Nat := fun j =>
    if x_coeffs ⟨j, by simp only; omega⟩ = 0 then 0 else 1
  let k := Nat.binaryFinMapToNat (n := steps) (m := k_bits) (h_binary := by
    intro j; simp only [k_bits]; split_ifs
    · norm_num
    · norm_num
  )
  exact k

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- When ϑ = 1, qMap_total_fiber maps k = 0 to an element with first coefficient 0
and k = 1 to an element with first coefficient 1. -/
lemma qMap_total_fiber_one_level_eq (i : Fin ℓ) (h_i_add_1 : i.val + 1 ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i + 1, by omega⟩)) (k : Fin 2) :
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
    let x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := 1) (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k
    let y_lifted : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ := sDomain.lift 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (h_j := by apply Nat.lt_add_of_pos_right_of_le; omega)
      (h_le := by apply Fin.mk_le_mk.mpr (by omega)) y
    let free_coeff_term : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ :=
      (Fin2ToF2 𝔽q k) • (basis_x ⟨0, by simp only; omega⟩)
    x = free_coeff_term + y_lifted
    := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
  apply basis_x.repr.injective
  simp only [map_add, map_smul]
  simp only [Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, basis_x]
  ext j
  have h_repr_x := qMap_total_fiber_repr_coeff 𝔽q β i (steps := 1) (by omega)
    (y := y) (k := k) (j := j)
  simp only [h_repr_x, Finsupp.coe_add, Pi.add_apply]
  simp only [fiber_coeff, lt_one_iff, reducePow, Fin2ToF2, Fin.isValue]

  by_cases hj : j = ⟨0, by omega⟩
  · simp only [hj, ↓reduceDIte, Fin.isValue, Finsupp.single_eq_same]
    by_cases hk : k = 0
    · simp only [getBit, hk, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, shiftRight_zero,
      and_one_is_mod, ↓reduceIte, zero_add]
      -- => Now use basis_repr_of_sDomain_lift
      simp only [basis_repr_of_sDomain_lift, add_tsub_cancel_left, zero_lt_one, ↓reduceDIte]
    · have h_k_eq_1 : k = 1 := by omega
      simp only [getBit, h_k_eq_1, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ, shiftRight_zero,
        Nat.and_self, one_ne_zero, ↓reduceIte, left_eq_add]
      simp only [basis_repr_of_sDomain_lift, add_tsub_cancel_left, zero_lt_one, ↓reduceDIte]
  · have hj_ne_zero : j ≠ ⟨0, by omega⟩ := by omega
    have hj_val_ne_zero : j.val ≠ 0 := by
      change j.val ≠ ((⟨0, by omega⟩ :  Fin (ℓ + 𝓡 - ↑i)).val)
      apply Fin.val_ne_of_ne
      exact hj_ne_zero
    simp only [hj_val_ne_zero, ↓reduceDIte, Finsupp.single, Fin.isValue, ite_eq_left_iff,
      one_ne_zero, imp_false, Decidable.not_not, Pi.single, Finsupp.coe_mk, Function.update,
      hj_ne_zero, Pi.zero_apply, zero_add]
    simp only [basis_repr_of_sDomain_lift, add_tsub_cancel_left, lt_one_iff, right_eq_dite_iff]
    intro hj_eq_zero
    exact False.elim (hj_val_ne_zero hj_eq_zero)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ [NeZero ℓ] in
/-- `x` is in the fiber of `y` under `qMap_total_fiber` iff `y` is the iterated
quotient of `x`. That is, for binary field, the fiber of `y` is exactly the set of
all `x` that map to `y` under the iterated quotient map. -/
theorem generates_quotient_point_if_is_fiber_of_y
    (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩))
    (hx_is_fiber : ∃ (k : Fin (2 ^ steps)), x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps) (h_i_add_steps := by
        simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (y := y) k) :
    y = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps) (h_bound := h_i_add_steps) x := by
 -- Get the fiber index `k` and the equality from the hypothesis.
  rcases hx_is_fiber with ⟨k, hx_eq⟩
  let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i.val + steps, by omega⟩) (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
  apply basis_y.repr.injective
  ext j
  conv_rhs =>
    rw [getSDomainBasisCoeff_of_iteratedQuotientMap]
  have h_repr_x := qMap_total_fiber_repr_coeff 𝔽q β i (steps := steps)
    (h_i_add_steps := by omega) (y := y) (k := k) (j := ⟨j + steps, by simp only; omega⟩)
  simp only at h_repr_x
  rw [←hx_eq] at h_repr_x
  simp only [fiber_coeff, add_lt_iff_neg_right, not_lt_zero', ↓reduceDIte, add_tsub_cancel_right,
    Fin.eta] at h_repr_x
  exact h_repr_x.symm

omit [CharP L 2] [NeZero ℓ] in
/-- State the corrrespondence between the forward qMap and the backward qMap_total_fiber -/
theorem is_fiber_iff_generates_quotient_point (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i.val + steps ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)) :
    let qMapFiber := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (y := y)
    let k := pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := h_i_add_steps) (x := x)
    y = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps) (h_bound := h_i_add_steps) x ↔
    qMapFiber k = x := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
    (by simp only; omega)
  let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩
    (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
  simp only
  set k := pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
    (h_i_add_steps := h_i_add_steps) (x := x)
  constructor
  · intro h_x_generates_y
    -- ⊢ qMap_total_fiber ...` ⟨↑i, ⋯⟩ steps ⋯ y k = x
    -- We prove that `qMap_total_fiber` with this `k` reconstructs `x` via basis repr
    apply basis_x.repr.injective
    ext j
    let reConstructedX := basis_x.repr (qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps) (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k)
    have h_repr_of_reConstructedX := qMap_total_fiber_repr_coeff 𝔽q β i (steps := steps)
      (h_i_add_steps := by omega) (y := y) (k := k) (j := j)
    simp only at h_repr_of_reConstructedX
    -- ⊢ repr of reConstructedX at j = repr of x at j
    rw [h_repr_of_reConstructedX]; dsimp [k, pointToIterateQuotientIndex, fiber_coeff];
    rw [getBit_of_binaryFinMapToNat]; simp only [Fin.eta, dite_eq_right_iff, ite_eq_left_iff,
      one_ne_zero, imp_false, Decidable.not_not]
    -- Now we only need to do case analysis
    by_cases h_j : j.val < steps
    · -- Case 1 : The first `steps` coefficients, determined by `k`.
      simp only [h_j, ↓reduceDIte, forall_const]
      by_cases h_coeff_j_of_x : basis_x.repr x j = 0
      · simp only [basis_x, h_coeff_j_of_x, ↓reduceIte];
      · simp only [basis_x, h_coeff_j_of_x, ↓reduceIte];
        have h_coeff := 𝔽q_element_eq_zero_or_eq_one 𝔽q (c := basis_x.repr x j)
        simp only [h_coeff_j_of_x, false_or] at h_coeff
        exact id (Eq.symm h_coeff)
    · -- Case 2 : The remaining coefficients, determined by `y`.
      simp only [h_j, ↓reduceDIte]
      simp only [basis_x]
      -- ⊢ Here we compare coeffs, not the basis elements
      simp only [h_x_generates_y]
      have h_res := getSDomainBasisCoeff_of_iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps)
        (h_bound := by omega) x (j := ⟨j - steps, by -- TODO : make this index bound proof cleaner
          simp only; rw [←Nat.sub_sub]; -- ⊢ ↑j - steps < ℓ + 𝓡 - ↑i - steps
          apply Nat.sub_lt_sub_right;
          · exact Nat.le_of_not_lt h_j
          · exact j.isLt
        ⟩) -- ⊢ ↑j - steps < ℓ + 𝓡 - (↑i + steps)
      have h_j_sub_add_steps : j - steps + steps = j := by omega
      simp only at h_res
      simp only [h_j_sub_add_steps, Fin.eta] at h_res
      exact h_res
  · intro h_x_is_fiber_of_y
    -- y is the quotient point of x over steps steps
    apply generates_quotient_point_if_is_fiber_of_y (h_i_add_steps := h_i_add_steps)
      (x := x) (y := y) (hx_is_fiber := by use k; exact h_x_is_fiber_of_y.symm)

omit [CharP L 2] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- the pointToIterateQuotientIndex of qMap_total_fiber -/
lemma pointToIterateQuotientIndex_qMap_total_fiber_eq_self (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩)) (k : Fin (2 ^ steps)) :
    pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps) (h_i_add_steps := by omega)
      (x := ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k):
          sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))) = k := by
  apply Fin.eq_mk_iff_val_eq.mpr
  apply eq_iff_eq_all_getBits.mpr
  intro j -- bit index j
  simp only [pointToIterateQuotientIndex, qMap_total_fiber]
  rw [Nat.getBit_of_binaryFinMapToNat]
  simp only [Nat.add_zero, Nat.pow_zero, eq_mp_eq_cast, cast_eq, Module.Basis.repr_symm_apply]
  by_cases h_j : j < steps
  · simp only [h_j, ↓reduceDIte];
    by_cases hsteps : steps = 0
    · simp only [hsteps, ↓reduceDIte, eqRec_eq_cast, Nat.add_zero, Nat.pow_zero]
      omega
    · simp only [hsteps, ↓reduceDIte, Module.Basis.repr_linearCombination,
      Finsupp.equivFunOnFinite_symm_apply_toFun, h_j, ite_eq_left_iff, one_ne_zero,
      imp_false, Decidable.not_not]
      -- ⊢ (if j.getBit ↑k = 0 then 0 else 1) = j.getBit ↑k
      have h := Nat.getBit_eq_zero_or_one (k := j) (n := k)
      by_cases h_j_getBit_k_eq_0 : j.getBit ↑k = 0
      · simp only [h_j_getBit_k_eq_0, ↓reduceIte]
      · simp only [h_j_getBit_k_eq_0, false_or, ↓reduceIte] at h ⊢
        exact id (Eq.symm h)
  · rw [Nat.getBit_of_lt_two_pow];
    simp only [h_j, ↓reduceDIte, ↓reduceIte];

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **qMap_fiber coefficient extraction** -/
lemma qMap_total_fiber_basis_sum_repr (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩))
    (k : Fin (2 ^ steps)) :
    let x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) := qMap_total_fiber 𝔽q β
      (i := ⟨i, by omega⟩) (steps := steps) (h_i_add_steps := by
        apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) (k)
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
      (by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
      (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
    let y_coeffs := basis_y.repr y
    x = ∑ j : Fin (ℓ + 𝓡 - i), (
      fiber_coeff (i := i) (steps := steps) (j := j) (elementIdx := k) (y_coeffs := y_coeffs)
    ) • (basis_x j)
     := by
    set basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by
      simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
    set basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
      (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
    set y_coeffs := basis_y.repr y
    -- Let `x` be the element from the fiber for brevity.
    set x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) (k)
    simp only;
    -- Express `(x:L)` using its basis representation, which is built from `x_coeffs_fn`.
    set x_coeffs_fn := fun j : Fin (ℓ + 𝓡 - i) =>
      fiber_coeff (i := i) (steps := steps) (j := j) (elementIdx := k) (y_coeffs := y_coeffs)
    have hx_val_sum : (x : L) = ∑ j, (x_coeffs_fn j) • (basis_x j) := by
      rw [←basis_x.sum_repr x]
      rw [Submodule.coe_sum, Submodule.coe_sum]
      congr; funext j;
      simp_rw [Submodule.coe_smul]
      congr; unfold x_coeffs_fn
      have h := qMap_total_fiber_repr_coeff 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (y := y) (k := k) (j := j)
      rw [h]
    apply Subtype.ext -- convert to equality in Subtype embedding
    rw [hx_val_sum]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
theorem card_qMap_total_fiber (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)) :
    Fintype.card (Set.image (qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
      (y := y)) Set.univ) = 2 ^ steps := by
  -- The cardinality of the image of a function equals the cardinality of its domain
  -- if it is injective.
  rw [Set.card_image_of_injective Set.univ]
  -- The domain is `Fin (2 ^ steps)`, which has cardinality `2 ^ steps`.
  · -- ⊢ Fintype.card ↑Set.univ = 2 ^ steps
    simp only [Fintype.card_setUniv, Fintype.card_fin]
  · -- prove that `qMap_total_fiber` is an injective function.
    intro k₁ k₂ h_eq
    -- Assume two indices `k₁` and `k₂` produce the same point `x`.
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
    -- If the points are equal, their basis representations must be equal.
    set fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)
    have h_coeffs_eq : basis_x.repr (fiberMap k₁) = basis_x.repr (fiberMap k₂) := by
      rw [h_eq]
    -- The first `steps` coefficients are determined by the bits of `k₁` and `k₂`.
    -- If the coefficients are equal, the bits must be equal.
    have h_bits_eq : ∀ j : Fin steps,
        Nat.getBit (k := j) (n := k₁.val) = Nat.getBit (k := j) (n := k₂.val) := by
      intro j
      have h_coeff_j_eq : basis_x.repr (fiberMap k₁) ⟨j, by simp only; omega⟩
        = basis_x.repr (fiberMap k₂) ⟨j, by simp only; omega⟩ := by rw [h_coeffs_eq]
      rw [qMap_total_fiber_repr_coeff 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := h_i_add_steps) (y := y) (j := ⟨j, by simp only; omega⟩)]
        at h_coeff_j_eq
      rw [qMap_total_fiber_repr_coeff 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := h_i_add_steps) (y := y) (k := k₂) (j := ⟨j, by simp only; omega⟩)]
        at h_coeff_j_eq
      simp only [fiber_coeff, Fin.is_lt, ↓reduceDIte] at h_coeff_j_eq
      by_cases hbitj_k₁ : Nat.getBit (k := j) (n := k₁.val) = 0
      · simp only [hbitj_k₁, ↓reduceIte, left_eq_ite_iff, zero_ne_one, imp_false,
        Decidable.not_not] at ⊢ h_coeff_j_eq
        simp only [h_coeff_j_eq]
      · simp only [hbitj_k₁, ↓reduceIte, right_eq_ite_iff, one_ne_zero,
        imp_false] at ⊢ h_coeff_j_eq
        have b1 : Nat.getBit (k := j) (n := k₁.val) = 1 := by
          have h := Nat.getBit_eq_zero_or_one (k := j) (n := k₁.val)
          simp only [hbitj_k₁, false_or] at h
          exact h
        have b2 : Nat.getBit (k := j) (n := k₂.val) = 1 := by
          have h := Nat.getBit_eq_zero_or_one (k := j) (n := k₂.val)
          simp only [h_coeff_j_eq, false_or] at h
          exact h
        simp only [b1, b2]
      -- Extract the j-th coefficient from h_coeffs_eq and show it implies the bits are equal.
    -- If all the bits of two numbers are equal, the numbers themselves are equal.
    apply Fin.eq_of_val_eq
    -- ⊢ ∀ {n : ℕ} {i j : Fin n}, ↑i = ↑j → i = j
    apply eq_iff_eq_all_getBits.mpr
    intro k
    by_cases h_k : k < steps
    · simp only [h_bits_eq ⟨k, by omega⟩]
    · -- The bits at positions ≥ steps must be deterministic
      conv_lhs => rw [Nat.getBit_of_lt_two_pow]
      conv_rhs => rw [Nat.getBit_of_lt_two_pow]
      simp only [h_k, ↓reduceIte]
omit [CharP L 2] [NeZero ℓ] in
/-- The images of `qMap_total_fiber` over distinct quotient points `y₁ ≠ y₂` are
disjoint -/
theorem qMap_total_fiber_disjoint
  (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
  {y₁ y₂ : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩}
  (hy_ne : y₁ ≠ y₂) :
  Disjoint
    ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) y₁ '' Set.univ).toFinset)
    ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) y₂ '' Set.univ).toFinset)
    := by
 -- Proof by contradiction. Assume the intersection is non-empty.
  rw [Finset.disjoint_iff_inter_eq_empty]
  by_contra h_nonempty
  -- Let `x` be an element in the intersection of the two fiber sets.
  obtain ⟨x, h_x_mem_inter⟩ := Finset.nonempty_of_ne_empty h_nonempty
  have hx₁ := Finset.mem_of_mem_inter_left h_x_mem_inter
  have hx₂ := Finset.mem_of_mem_inter_right h_x_mem_inter
  -- A helper lemma : applying the forward map to a point in a generated fiber returns
  -- the original quotient point.
  have iteratedQuotientMap_of_qMap_total_fiber_eq_self
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩)
    (k : Fin (2 ^ steps)) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (k := steps)
      (h_bound := by omega)
      (qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k) = y := by
      have h := generates_quotient_point_if_is_fiber_of_y
        (h_i_add_steps := h_i_add_steps) (x:=
        ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k) :
          sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))
      ) (y := y) (hx_is_fiber := by use k)
      exact h.symm
  have h_exists_k₁ : ∃ k, x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y₁ k := by
    -- convert (x ∈ Finset of the image of the fiber) to statement
    -- about membership in the Set.
    rw [Set.mem_toFinset] at hx₁
    rw [Set.mem_image] at hx₁ -- Set.mem_image gives us t an index that maps to x
    -- ⊢ `∃ (k : Fin (2 ^ steps)), k ∈ Set.univ ∧ qMap_total_fiber ... y₁ k = x`.
    rcases hx₁ with ⟨k, _, h_eq⟩
    use k; exact h_eq.symm

  have h_exists_k₂ : ∃ k, x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y₂ k := by
    rw [Set.mem_toFinset] at hx₂
    rw [Set.mem_image] at hx₂ -- Set.mem_image gives us t an index that maps to x
    rcases hx₂ with ⟨k, _, h_eq⟩
    use k; exact h_eq.symm

  have h_y₁_eq_quotient_x : y₁ =
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x := by
    apply generates_quotient_point_if_is_fiber_of_y (hx_is_fiber := by exact h_exists_k₁)

  have h_y₂_eq_quotient_x : y₂ =
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x := by
    apply generates_quotient_point_if_is_fiber_of_y (hx_is_fiber := by exact h_exists_k₂)

  let kQuotientIndex := pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
    (h_i_add_steps := by omega) (x := x)

  -- Since `x` is in the fiber of `y₁`, applying the forward map to `x` yields `y₁`.
  have h_map_x_eq_y₁ : iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
      (k := steps) (h_bound := by omega) x = y₁ := by
    have h := iteratedQuotientMap_of_qMap_total_fiber_eq_self (y := y₁) (k := kQuotientIndex)
    have hx₁ : x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y₁ kQuotientIndex := by
      have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
        (x := x) (y := y₁).mp (h_y₁_eq_quotient_x)
      exact h_res.symm
    rw [hx₁]
    exact iteratedQuotientMap_of_qMap_total_fiber_eq_self y₁ kQuotientIndex

  -- Similarly, since `x` is in the fiber of `y₂`, applying the forward map yields `y₂`.
  have h_map_x_eq_y₂ : iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
      (k := steps) (h_bound := by omega) x = y₂ := by
    -- have h := iteratedQuotientMap_of_qMap_total_fiber_eq_self (y := y₂) (k := kQuotientIndex)
    have hx₂ : x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y₂ kQuotientIndex := by
      have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
        (x := x) (y := y₂).mp (h_y₂_eq_quotient_x)
      exact h_res.symm
    rw [hx₂]
    exact iteratedQuotientMap_of_qMap_total_fiber_eq_self y₂ kQuotientIndex

  exact hy_ne (h_map_x_eq_y₁.symm.trans h_map_x_eq_y₂)

/-- Single-step fold : Given `f : S⁽ⁱ⁾ → L` and challenge `r`, produce `S⁽ⁱ⁺¹⁾ → L`, where
`f⁽ⁱ⁺¹⁾ = fold(f⁽ⁱ⁾, r) : y ↦ [1-r, r] · [[x₁, -x₀], [-1, 1]] · [f⁽ⁱ⁾(x₀), f⁽ⁱ⁾(x₁)]`
-/
def fold (i : Fin r) (h_i : i + 1 < ℓ + 𝓡) (f : (sDomain 𝔽q β
    h_ℓ_add_R_rate) i → L) (r_chal : L) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) (⟨i + 1, by omega⟩) → L :=
  fun y => by
    let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := 1)
      (h_i_add_steps := h_i) (y := y)
    let x₀ := fiberMap 0
    let x₁ := fiberMap 1
    let f_x₀ := f x₀
    let f_x₁ := f x₁
    exact f_x₀ * ((1 - r_chal) * x₁.val - r_chal) + f_x₁ * (r_chal - (1 - r_chal) * x₀.val)

/-- Helper to cast matrices between equal dimensions (needed for 2^(k+1) = 2^k + 2^k) -/
@[reducible, simp]
def reindexSquareMatrix {n m : Type} (e : n ≃ m) (M : Matrix n n L) : Matrix m m L :=
  Matrix.reindex (α := L) (eₘ := e) (eₙ := e) M

def butterflyMatrix (n : ℕ) (z₀ z₁ : L) : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
    -- 4. Construct the Butterfly Matrix using Scalar Identities
    --    [ z₁*I_{2^n}   -z₀*I_{2^n} ]
    --    [ -1*I_{2^n}     1*I_{2^n} ]
    let I_n : Matrix (Fin (2^n)) (Fin (2^n)) L := 1 -- Identity matrix
    let butterfly : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
      reindexSquareMatrix (e := finCongr (by omega)) (M := Matrix.from4Blocks
                                                (z₁ • I_n)  (-(z₀ • I_n))
                                                ((-1 : L) • I_n) ((1 : L) • I_n))
    butterfly

omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- Characterization of butterflyMatrix at `n=0` (used in single-step folding). -/
@[simp]
lemma butterflyMatrix_zero_apply (z₀ z₁ : L) :
    butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := 0) z₀ z₁ = !![z₁, -z₀; -1, 1] := by
  rw [butterflyMatrix]
  simp only [reduceAdd, reducePow, reindexSquareMatrix, Nat.pow_zero, finCongr_refl, neg_smul,
    one_smul, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, submatrix_id_id]
  unfold Matrix.from4Blocks
  simp only [reduceAdd, lt_one_iff, Fin.val_eq_zero_iff, Fin.isValue, smul_apply, smul_eq_mul,
    neg_apply]
  funext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceDIte, one_apply_eq, mul_one, of_apply, cons_val',
    cons_val_zero, cons_val_fin_one] -- 0, 0 (Top Left)
  · -- 0, 1 (Top Right)
    simp only [Fin.zero_eta, Fin.isValue, ↓reduceDIte, Fin.mk_one, one_ne_zero, of_apply,
    cons_val', cons_val_one, cons_val_fin_one, cons_val_zero, neg_inj];
    rw [Matrix.one_apply]
    simp only [Fin.zero_eta, Fin.isValue, tsub_self, ↓reduceIte, mul_one]
  · rfl -- 1, 0 (Bottom Left)
  · rfl -- 1, 1 (Bottom Right)

omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
lemma butterflyMatrix_det_ne_zero (n : ℕ) (z₀ z₁ : L) (h_ne : z₀ ≠ z₁) :
  (butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := n) z₀ z₁).det ≠ 0 := by
  -- Proof: det is (z₁ - z₀)^(2^n)
  -- 1. Use Matrix.det_from4Blocks (since blocks commute)
  -- 2. Simplify to det((z₁ - z₀) • I)
  -- 3. Use Matrix.det_smul and h_ne
  dsimp only [butterflyMatrix]
  -- The matrix is:
  -- [ z₁*I   -z₀*I ]
  -- [ -1*I    1*I  ]
  -- Since the blocks commute (scalar multiples of identity), det(M) = det(AD - BC)
  -- AD - BC = (z₁*I)(I) - (-z₀*I)(-I) = z₁*I - z₀*I = (z₁ - z₀)*I
  rw [Matrix.det_reindex_self]
  rw [Matrix.det_from4Blocks_of_squareSubblocks_commute]
  · -- Calculate the determinant of the combined block
    rw [one_smul, mul_one, Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal]
    -- ⊢ ((diagonal fun x ↦ z₁) - (-diagonal fun x ↦ z₀) * -1 • 1).det ≠ 0
    simp only [diagonal_neg, neg_smul, one_smul, mul_neg, mul_one, neg_neg, diagonal_sub,
      det_diagonal, prod_const, Finset.card_univ, Fintype.card_fin, ne_eq, Nat.pow_eq_zero,
      OfNat.ofNat_ne_zero, false_and, not_false_eq_true, pow_eq_zero_iff]
    -- ⊢ ¬z₁ - z₀ = 0
    exact sub_ne_zero_of_ne (Ne.symm h_ne)
  · -- Prove the blocks commute
    -- The bottom-right block is `1 • I = I`, which commutes with everything.
    -- ⊢ Commute (-1 • 1) (1 • 1)
    simp only [neg_smul, one_smul, Commute.one_right]

/-- `BlkDiagMat(n, Mz₀, Mz₁) = [Mz₀, 0;`
                                   `0, Mz₁]`
where `Mz₀` and `Mz₁` are set as the `n-step` `foldMatrix` of `z₀` and `z₁` in **Lemma 4.9**. -/
def blockDiagMatrix (n : ℕ)
    (Mz₀ Mz₁ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) L) :
    Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
  let zero_blk : Matrix (Fin (2^n)) (Fin (2^n)) L := 0
  let blk_diag : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
    reindexSquareMatrix (e := finCongr (by omega))
      (M := Matrix.from4Blocks Mz₀ zero_blk zero_blk Mz₁)
  blk_diag

omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- Block Diagonal matrix multiplication on top half returns M_top * v_top
Proof similar to challengeTensorExpansionMatrix_mulVec_F₂_eq_Fin_merge_PO2.
-/
lemma blockDiagMatrix_mulVec_F₂_eq_Fin_merge_PO2 (n : ℕ)
    (A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) L)
    (v_top : Fin (2 ^ n) → L) (v_bot : Fin (2 ^ n) → L) :
    mergeFinMap_PO2_left_right (left := A *ᵥ v_top) (right := B *ᵥ v_bot)
    = blockDiagMatrix (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (n := n) (Mz₀ := A) (Mz₁ := B)
      *ᵥ mergeFinMap_PO2_left_right (left := v_top) (right := v_bot) := by
  dsimp only [blockDiagMatrix]
  conv_rhs => -- Move reindexing from Matrix to Vector
    rw [Matrix.reindex_mulVec]
  funext k
  unfold mergeFinMap_PO2_left_right
  unfold Matrix.from4Blocks Fin.reindex Matrix.mulVec dotProduct
  -- Now unfold everything
  simp only [zero_apply, finCongr_symm, Function.comp_apply, finCongr_apply, dite_mul, zero_mul,
    sum_dite_irrel, Fin.coe_cast]
  simp_rw [Fin.sum_univ_add]
  simp_rw [←Finset.sum_add_distrib]
  simp only [Fin.coe_castAdd, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.natAdd_eq_addNat, Fin.coe_addNat,
    add_lt_iff_neg_right, not_lt_zero', add_zero, add_tsub_cancel_right, zero_add]

/-- The recursive definition of the `k-step` fold matrix of point `y`: `M_{k, y}`.
`M_{k, y} = butterflyMatrix(k, z₀, z₁) * [M_{k-1, z₀}, 0; 0, M_{k-1, z₁}]`
where `z₀` and `z₁` are the 1-step fiber of `y`. `M_{k, y}` is actually the
`inverse additive NTT (LCH14)` on the coset `(x₀, ..., x_{2^k-1})` **(Remark 4.10)**. -/
def foldMatrix (i : Fin r) (steps : ℕ) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩) :
    Matrix (Fin (2 ^ steps)) (Fin (2 ^ steps)) L :=
  match steps with
  | 0 =>
    -- Base case: steps = 0. Identity matrix of size 1 (2^0).
    (1 : Matrix (Fin 1) (Fin 1) L) -- diagonal matrix
  | n + 1 => by
    -- Recursive step: n -> n + 1
    -- 1. Identify the "previous" y's (z₀ and z₁) from the fiber of the current y
    --    Note: y is at index i + n + 1. We need the fiber at i + n.
    let prev_idx : Fin r := ⟨i + n, by omega⟩
    have h_prev_idx_val : prev_idx.val = i + n := by dsimp only [prev_idx]
    let fiberMap := qMap_total_fiber 𝔽q β (i := prev_idx) (steps := 1)
       (h_i_add_steps := h_i_add_steps) (y := y)

    let z₀ : sDomain 𝔽q β h_ℓ_add_R_rate prev_idx := fiberMap 0
    let z₁ : sDomain 𝔽q β h_ℓ_add_R_rate prev_idx := fiberMap 1

    -- 2. Recursively compute M for z₀ and z₁
    --    These matrices have size 2^n x 2^n
    let M_z₀ := foldMatrix i n (by omega) z₀
    let M_z₁ := foldMatrix i n (by omega) z₁

    -- 3. Construct the Block Diagonal Matrix: [ M_z₀  0  ]
    --                                         [  0   M_z₁]
    let blk_diag : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
      blockDiagMatrix (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (n := n) (Mz₀ := M_z₀) (Mz₁ := M_z₁)

    -- 4. Construct the Butterfly Matrix using Scalar Identities
    --    [ z₁*I_{2^n}   -z₀*I_{2^n} ]
    --    [ -1*I_{2^n}     1*I_{2^n} ]
    let butterfly : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) L :=
      butterflyMatrix (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (n := n) (z₀ := z₀) (z₁ := z₁)

    exact butterfly * blk_diag

lemma foldMatrix_det_ne_zero (i : Fin ℓ) (steps : ℕ) (h_i : i + steps ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (⟨i + steps, by omega⟩)) :
    (foldMatrix (i := ⟨i, by omega⟩) (steps := steps) (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)).det ≠ 0 := by
  induction steps with
  | zero => simp only [Nat.pow_zero, foldMatrix, det_unique, one_apply_eq, ne_eq, one_ne_zero,
    not_false_eq_true];
  | succ n ih =>
    rw [foldMatrix]
    -- 1. Determinant of product = product of determinants
    -- 2. det(butterfly) ≠ 0 because z₀ ≠ z₁ (by injectivity of qMap_total_fiber)
    -- 3. det(block_diag) ≠ 0 because det(M_z₀) ≠ 0 and det(M_z₁) ≠ 0 (by IH)
    -- Expand definition of foldMatrix for n+1
    dsimp [foldMatrix]
    -- Determinant of product
    rw [Matrix.det_mul]
    let prev_idx : Fin r := ⟨i + n, by omega⟩
    let fiberMap := qMap_total_fiber 𝔽q β (i := prev_idx) (steps := 1) (h_i_add_steps := by
      apply Nat.lt_add_of_pos_right_of_le; dsimp only [prev_idx]; omega) (y := y)
    let z₀ := fiberMap 0
    let z₁ := fiberMap 1
    apply mul_ne_zero
    -- 1. Butterfly Matrix part
    · -- ⊢ Δ(butterflyMatrix(n, z₀, z₁)) ≠ 0
      apply butterflyMatrix_det_ne_zero (L := L) (z₀ := z₀) (z₁ := z₁) (n := n)
      -- ⊢ ↑z₀ ≠ ↑z₁
      unfold z₀ z₁ fiberMap
      let z₀_eq := qMap_total_fiber_one_level_eq (i := ⟨prev_idx, by dsimp [prev_idx]; omega⟩)
        (h_i_add_1 := by omega) (y := y) (k := 0)
      let z₁_eq := qMap_total_fiber_one_level_eq (i := ⟨prev_idx, by dsimp [prev_idx]; omega⟩)
        (h_i_add_1 := by omega) (y := y) (k := 1)
      conv_lhs => rw [z₀_eq]
      conv_rhs => rw [z₁_eq]
      simp only [Fin.eta, Fin.isValue, Submodule.coe_add, SetLike.val_smul, ne_eq, add_left_inj]
      unfold Fin2ToF2
      rw [get_sDomain_first_basis_eq_1]
      simp only [Fin.isValue, ↓reduceIte, zero_smul, one_ne_zero, one_smul, zero_ne_one,
        not_false_eq_true]
    -- 2. Block Diagonal Part
    · dsimp only [blockDiagMatrix]
      rw [Matrix.det_reindex_self]
      rw [Matrix.det_from4Blocks_of_squareSubblocks_commute]
      -- Diagonal blocks: M_z₀ and M_z₁. Off-diagonal: 0.
      -- det(M) = det(M_z₀) * det(M_z₁) - 0*0
      · simp only [Fin.isValue, mul_zero, sub_zero, det_mul, ne_eq, _root_.mul_eq_zero, not_or]
       -- ⊢ `(Δ(M_z₀) ≠ 0 ∧ Δ(M_z₁) ≠ 0)`
        have h_det_M_z₀_ne_zero := ih (by omega) (y := z₀)
        have h_det_M_z₁_ne_zero := ih (by omega) (y := z₁)
        constructor
        · exact h_det_M_z₀_ne_zero
        · exact h_det_M_z₁_ne_zero
      · simp only [Fin.isValue, Commute.zero_left]

/-- **Definition 4.8**: Iterated fold over `steps` steps starting at domain index `i`. -/
def iterated_fold (i : Fin r) (steps : ℕ) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
  (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L) (r_challenges : Fin steps → L) :
    (y : sDomain 𝔽q β h_ℓ_add_R_rate
      (⟨i + steps, Nat.lt_trans (m := ℓ + 𝓡) (h_i_add_steps) h_ℓ_add_R_rate⟩)) → L := by
  let domain_type := sDomain 𝔽q β h_ℓ_add_R_rate
  let fold_func := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  let α (j : Fin (steps + 1)) := domain_type (⟨i + j.val, by omega⟩) → L
  let fold_step (j : Fin steps) (f_acc : α ⟨j, by omega⟩) : α j.succ := by
    unfold α domain_type at *
    intro x
    have fold_func := fold_func (i := ⟨i + j.val, by omega⟩) (h_i := by
      simp only
      omega
    ) (f_acc) (r_challenges j)
    exact fold_func x
  exact Fin.dfoldl (n := steps) (α := α) (f := fun i (accF : α ⟨i, by omega⟩) =>
    have fSucc : α ⟨i.succ, by omega⟩ := fold_step i accF
    fSucc) (init := f)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
lemma iterated_fold_last (i : Fin r) (steps : ℕ) (h_i_add_steps : i.val + steps + 1 < ℓ + 𝓡)
  (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L) (r_challenges : Fin (steps + 1) → L) :
  let fold_full := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    (steps := steps + 1) (h_i_add_steps := h_i_add_steps) (f := f) (r_challenges := r_challenges)
  let fold_init := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    (steps := steps) (h_i_add_steps := by omega) (f := f) (r_challenges := Fin.init r_challenges)
  let fold_init_fold := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := by omega)
    (f := fold_init) (r_chal := r_challenges (Fin.last steps))
  fold_full = fold_init_fold := by
  simp only
  conv_lhs => unfold iterated_fold
  rw [Fin.dfoldl_succ_last]
  rfl

/--
Transitivity of iterated_fold : folding for `steps₁` and then for `steps₂`
equals folding for `steps₁ + steps₂` with concatenated challenges.
-/
lemma iterated_fold_transitivity
    (i : Fin r) (steps₁ steps₂ : Fin (ℓ + 1))
    (h_bounds : i.val + steps₁ + steps₂ ≤ ℓ) -- A single, sufficient bounds check
    (f : sDomain 𝔽q β h_ℓ_add_R_rate (i := i) → L)
    (r_challenges₁ : Fin steps₁ → L) (r_challenges₂ : Fin steps₂ → L) :
    -- LHS : The nested fold (folding twice)
    have hi1 : i.val + steps₁ ≤ ℓ := by exact le_of_add_right_le h_bounds
    have hi2 : i.val + steps₂ ≤ ℓ := by
      rw [Nat.add_assoc, Nat.add_comm steps₁ steps₂, ←Nat.add_assoc] at h_bounds
      exact le_of_add_right_le h_bounds
    have hi12 : steps₁ + steps₂ < ℓ + 1 := by
      apply Nat.lt_succ_of_le; rw [Nat.add_assoc] at h_bounds;
      exact Nat.le_of_add_left_le h_bounds
    let lhs := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i.val + steps₁, by -- ⊢ ↑i + ↑steps₁ < r
        apply Nat.lt_of_le_of_lt (m := ℓ) (hi1) (ℓ_lt_r (h_ℓ_add_R_rate := h_ℓ_add_R_rate))⟩)
      (steps := steps₂)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; exact h_bounds)
      (f := by
        exact iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps₁)
          (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; exact hi1) (f := f)
          (r_challenges := r_challenges₁)
      ) r_challenges₂
    let rhs := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps₁.val + steps₂.val)
      (h_i_add_steps := by
        rw [←Nat.add_assoc]; apply Nat.lt_add_of_pos_right_of_le; exact h_bounds)
      (f := f) (r_challenges := Fin.append r_challenges₁ r_challenges₂)
    lhs = by
      simp only [←Nat.add_assoc] at ⊢ rhs
      exact rhs := by
  sorry -- admitted for brevity, relies on a lemma like `Fin.dfoldl_add`

/-- Evaluation vector `[f^(i)(x_0) ... f^(i)(x_{2 ^ steps-1})]^T`. This is the rhs
vector in the identity in **Lemma 4.9** -/
def fiberEvaluations (i : Fin r) (steps : ℕ) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) i → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨↑i + steps, by apply Nat.lt_trans (m := ℓ + 𝓡) (h_i_add_steps) h_ℓ_add_R_rate⟩)
    : Fin (2 ^ steps) → L :=
  -- Get the fiber points
  let fiberMap := qMap_total_fiber 𝔽q β (i := i) (steps := steps)
    (h_i_add_steps := h_i_add_steps) (y := y)

  -- Evaluate f at each fiber point
  fun idx => f (fiberMap idx)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
lemma fiberEvaluations_eq_merge_fiberEvaluations_of_one_step_fiber (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i + steps + 1 ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + steps + 1, by omega⟩) :
    let fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i+steps, by omega⟩) (steps := 1)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)
    let z₀ := fiberMap 0
    let z₁ := fiberMap 1
    let fiber_eval_z₀ : Fin (2 ^ steps) → L := fiberEvaluations 𝔽q β (steps := steps)
      (i := ⟨i, by omega⟩)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) f z₀
    let fiber_eval_z₁ : Fin (2 ^ steps) → L := fiberEvaluations 𝔽q β (steps := steps)
      (i := ⟨i, by omega⟩)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) f z₁
    (fiberEvaluations 𝔽q β (steps := steps + 1) (i := ⟨i, by omega⟩)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) f y) =
    mergeFinMap_PO2_left_right (left := fiber_eval_z₀) (right := fiber_eval_z₁) := by
  -- 1. Unfold definitions to expose `qMap_total_fiber`
  unfold fiberEvaluations mergeFinMap_PO2_left_right
  simp only
  funext fiber_y_idx -- fiber_y_idx is index of the `steps`-step fiber point of y (y ∈ S^{i+steps})
  -- 2. We need to show that the fiber point mapping splits correctly.
  -- Split into cases based on the MSB of fiber_y_idx
  set fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i+steps, by omega⟩) (steps := 1)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)
  set z₀ := fiberMap 0
  set z₁ := fiberMap 1
  set left_point := (qMap_total_fiber (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (steps := steps + 1)
    (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)) (y := y)
      fiber_y_idx
  -- ⊢ f left_point = if h : ↑fiber_y_idx < 2 ^ steps then
      -- f (qMap_total_fiber 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ z₀ ⟨↑fiber_y_idx, ⋯⟩)
  --   else f (qMap_total_fiber 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ z₁ ⟨↑fiber_y_idx - 2 ^ steps, ⋯⟩)
  let zᵢ : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩ :=
    if h : fiber_y_idx.val < 2 ^ steps then z₀ else z₁
  let fiber_zᵢ_idx : Fin (2 ^ steps) :=
    if h : fiber_y_idx.val < 2 ^ steps then ⟨fiber_y_idx, by omega⟩
    else ⟨fiber_y_idx.val - 2 ^ steps, by omega⟩

  set right_point := qMap_total_fiber (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (steps := steps)
    (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
    (y := zᵢ) fiber_zᵢ_idx

  have h_left_point_eq_right_point : left_point = right_point := by
    let basis := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
    apply basis.repr.injective
    ext (coeffIdx : Fin (ℓ + 𝓡 - i))
    rw [qMap_total_fiber_repr_coeff 𝔽q β ⟨i, by omega⟩ (steps := steps + 1)
      (h_i_add_steps := by simp only; omega) (y := y) (k := fiber_y_idx)]
    rw [qMap_total_fiber_repr_coeff 𝔽q β ⟨i, by omega⟩ (steps := steps)
      (h_i_add_steps := by simp only; omega) (y := zᵢ) (k := fiber_zᵢ_idx)]
    dsimp only [Fin.eta, fiber_coeff]
    unfold zᵢ fiber_zᵢ_idx
    --   ⊢ (if hj : ↑j < steps + 1 then if (↑j).getBit ↑fiber_y_idx = 0 then 0 else 1
    -- else ((S^(i+steps+1)).repr y) ⟨↑j - (steps + 1), ⋯⟩) =
    -- if hj : ↑j < steps then if (↑j).getBit ↑fiber_zᵢ_idx = 0 then 0 else 1
    -- else ((sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨↑i + steps, ⋯⟩ ⋯).repr zᵢ) ⟨↑j - steps, ⋯⟩
    have h_repr_z₀ := qMap_total_fiber_repr_coeff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i + steps, by omega⟩) (steps := 1) (h_i_add_steps := by simp only; omega)
      (y := y) (k := 0)
    have h_repr_z₁ := qMap_total_fiber_repr_coeff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i + steps, by omega⟩) (steps := 1) (h_i_add_steps := by simp only; omega)
      (y := y) (k := 1)

    by_cases h_fiber_y_idx_lt_2_pow_steps : fiber_y_idx.val < 2 ^ steps
    · -- right-point is qMap_total_fiber(z₀, fiber_y_idx)
      simp only [h_fiber_y_idx_lt_2_pow_steps, ↓reduceDIte]
      by_cases h_coeffIdx_lt_steps : coeffIdx.val < steps
      · have h_lt_succ : coeffIdx.val < steps + 1 := by omega
        simp only [h_lt_succ, ↓reduceDIte, h_coeffIdx_lt_steps]
      · simp only [h_coeffIdx_lt_steps, ↓reduceDIte]
        by_cases h_lt_succ : coeffIdx.val < steps + 1
        · simp only [h_lt_succ, ↓reduceDIte]
          have h_repr_z₀_rhs := h_repr_z₀ ⟨coeffIdx.val - steps, by omega⟩
          conv_rhs => rw [h_repr_z₀_rhs]
          unfold fiber_coeff
          simp only [lt_one_iff, reducePow, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod]
          have h_coeffIdx_eq_steps : coeffIdx.val = steps := by omega
          simp only [h_coeffIdx_eq_steps, tsub_self, ↓reduceDIte]

          have h_steps_getBit_idx : Nat.getBit (n := fiber_y_idx) (k := steps) = 0 := by
            let res := Nat.getBit_of_lt_two_pow (k := steps) (n := steps)
              (a := ⟨fiber_y_idx, by omega⟩)
            simp only [lt_self_iff_false, ↓reduceIte] at res
            exact res
          rw [h_steps_getBit_idx, Nat.getBit]
          simp only [↓reduceIte, shiftRight_zero, and_one_is_mod, zero_mod]
        · simp only [h_lt_succ, ↓reduceDIte]
          have h_repr_z₀_rhs := h_repr_z₀ ⟨coeffIdx.val - steps, by simp only; omega⟩
          conv_rhs => rw [h_repr_z₀_rhs]
          unfold fiber_coeff
          simp only [lt_one_iff, reducePow, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod]
          have h_sub_gt_0: coeffIdx.val - steps ≠ 0 := by omega
          simp only [h_sub_gt_0, ↓reduceDIte]
          rfl
    · -- right-point is qMap_total_fiber(z₁, fiber_y_idx - 2 ^ steps)
      have h_fiber_y_idx_ge_2_pow_steps : fiber_y_idx.val ≥ 2 ^ steps := by omega
      have h_fiber_y_idx_getBit_steps : Nat.getBit (k := steps) (n := fiber_y_idx) = 1 := by
        -- This is because 2^steps ≤ fiber_y_idx.val < 2^(steps + 1)
        have h_lt : fiber_y_idx.val < 2^(steps + 1) := by omega
        apply Nat.getBit_1_of_ge_two_pow_and_lt_two_pow_succ; omega; omega
      simp only [h_fiber_y_idx_lt_2_pow_steps, ↓reduceDIte]
      by_cases h_coeffIdx_lt_steps : coeffIdx.val < steps
      · have h_lt_succ : coeffIdx.val < steps + 1 := by omega
        simp only [h_lt_succ, ↓reduceDIte, h_coeffIdx_lt_steps]
        -- ⊢ (if (↑coeffIdx).getBit ↑fiber_y_idx = 0 then 0 else 1) =
        -- if (↑coeffIdx).getBit (↑fiber_y_idx - 2 ^ steps) = 0 then 0 else 1
        have h_getBit_eq: Nat.getBit (n := fiber_y_idx) (k := coeffIdx)
          = Nat.getBit (n := fiber_y_idx - 2 ^ steps) (k := coeffIdx) := by
          let getBit_Sub_2_pow_steps := Nat.getBit_of_sub_two_pow_of_bit_1 (n := fiber_y_idx)
            (i := steps) (h_getBit_eq_1 := h_fiber_y_idx_getBit_steps) (j := coeffIdx)
          rw [getBit_Sub_2_pow_steps]
          have h_ne : coeffIdx.val ≠ steps := by omega
          simp only [h_ne, ↓reduceIte]
        rw [h_getBit_eq]
      · simp only [h_coeffIdx_lt_steps, ↓reduceDIte]
        by_cases h_lt_succ : coeffIdx.val < steps + 1
        · simp only [h_lt_succ, ↓reduceDIte]
          have h_repr_z₁_rhs := h_repr_z₁ ⟨coeffIdx.val - steps, by omega⟩
          conv_rhs => rw [h_repr_z₁_rhs]
          unfold fiber_coeff
          simp only [lt_one_iff, reducePow, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ]
          have h_coeffIdx_eq_steps : coeffIdx.val = steps := by omega
          simp only [h_coeffIdx_eq_steps, tsub_self, ↓reduceDIte]
          simp only [h_fiber_y_idx_getBit_steps, one_ne_zero, ↓reduceIte, right_eq_ite_iff,
            imp_false, ne_eq];
          simp only [getBit, shiftRight_zero, Nat.and_self, one_ne_zero, not_false_eq_true]
        · simp only [h_lt_succ, ↓reduceDIte]
          have h_repr_z₁_rhs := h_repr_z₁ ⟨coeffIdx.val - steps, by simp only; omega⟩
          conv_rhs => rw [h_repr_z₁_rhs]
          unfold fiber_coeff
          simp only [lt_one_iff, reducePow, Fin.isValue, Fin.coe_ofNat_eq_mod]
          have h_sub_gt_0: coeffIdx.val - steps ≠ 0 := by omega
          simp only [h_sub_gt_0, ↓reduceDIte]
          rfl
  rw [h_left_point_eq_right_point]
  unfold right_point zᵢ fiber_zᵢ_idx
  split_ifs with h_lt
  · simp only -- z₀
  · simp only -- z₁

/-- **Definition 4.6** : the single-step vector-matrix-vector multiplication form of `fold` -/
def fold_single_matrix_mul_form (i : Fin ℓ) (h_i_add_steps : i.val + 1 ≤ ℓ)
  (f : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by
        exact Fin.is_le') (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L)
  (r_challenge : L) : (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + 1, by omega⟩) → L :=
  fun y => by
    let fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := 1)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)
    let fiber_eval_mapping : (Fin 2) → L := fiberEvaluations 𝔽q β (steps := 1)
      (i := ⟨i, by omega⟩) (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) f y

    let z₀ : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ := fiberMap 0
    let z₁ : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ := fiberMap 1

    let challenge_vec : Fin (2 ^ 1) → L :=
      challengeTensorExpansion (n := 1) (r := fun _ => r_challenge)

    let fold_mat : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) L :=
      butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := 0) (z₀ := z₀) (z₁ := z₁)
    -- Matrix-vector multiplication : challenge_vec^T • (fold_mat • fiber_eval_mapping)
    let intermediate_fn := Matrix.mulVec fold_mat fiber_eval_mapping -- rhs Mat-Vec mul
    exact dotProduct challenge_vec intermediate_fn -- vec-vec dot product

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- The equality between the 1-step point-wise fold() operation vs the vec-mat-vec
multiplication form from **Definition 4.6** -/
lemma fold_eval_single_matrix_mul_form (i : Fin ℓ) (h_i_add_steps : i.val + 1 ≤ ℓ)
  (f : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by
        exact Fin.is_le') (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L)
  (r_challenge : L) :
  fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (f := f)
    (h_i := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (r_chal := r_challenge)
  = fold_single_matrix_mul_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
    (h_i_add_steps := h_i_add_steps) (f := f) (r_challenge := r_challenge) := by
  unfold fold_single_matrix_mul_form fold
  funext y
  simp only [Fin.isValue, reducePow, Fin.eta, vec2_dotProduct]
  -- Approach: decompose the rhs into a flat sum expression
  have h_chal_tensor_vec_eq : challengeTensorExpansion (n := 1) (r := fun _ => r_challenge)
    = ![1 - r_challenge, r_challenge] := by
      unfold challengeTensorExpansion multilinearWeight
      simp only [reducePow, univ_unique, Fin.default_eq_zero, Fin.isValue, Fin.val_eq_zero,
        testBit_zero, decide_eq_true_eq, prod_ite_irrel, prod_const, card_singleton, pow_one,
        succ_eq_add_one, reduceAdd]
      funext i
      by_cases h : i = 0
      · simp only [h, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, zero_ne_one, ↓reduceIte,
        cons_val_zero]
      · have h_i_eq_1 : i = 1 := by omega
        simp only [h_i_eq_1, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ, ↓reduceIte, cons_val_one,
          cons_val_fin_one]
  set fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := 1)
    (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)
  set z₀ := fiberMap 0
  set z₁ := fiberMap 1
  let butterflyMat0 := butterflyMatrix_zero_apply (L := L) (𝓡 := 𝓡) (ℓ := ℓ) (r := r)
    (z₀ := z₀) (z₁ := z₁)
  conv_rhs => rw [butterflyMat0];
  conv_rhs =>
    unfold fiberEvaluations
    rw! [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
    simp only [Fin.isValue, Fin.sum_univ_two]
    rw [h_chal_tensor_vec_eq]
    simp only [succ_eq_add_one, reduceAdd, Fin.isValue, cons_val_zero, reindexSquareMatrix,
      reducePow, finCongr_refl, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, submatrix_apply,
      id_eq, cons_val_one, cons_val_fin_one]
  conv_rhs =>
    unfold Matrix.from4Blocks
    simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
      neg_mul, one_mul]
  unfold z₀ z₁ fiberMap -- this helps Lean understand the goal better
  ring_nf


/-- The single point vec-mat-vec form of `fold(...)` in **Lemma 4.9** -/
def single_point_localized_fold_matrix_form (i : Fin ℓ) (steps : ℕ)
  (h_i_add_steps : i.val + steps ≤ ℓ)
  (r_challenges : Fin steps → L)
  (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩)
  (fiber_eval_mapping : Fin (2 ^ steps) → L) :
  L := by
    let challenge_vec : Fin (2 ^ steps) → L :=
      challengeTensorExpansion (n := steps) (r := r_challenges)
    let fold_mat : Matrix (Fin (2 ^ steps)) (Fin (2 ^ steps)) L :=
      foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)
    -- Matrix-vector multiplication : challenge_vec^T • (fold_mat • fiber_eval_mapping)
    let intermediate_fn := Matrix.mulVec fold_mat fiber_eval_mapping -- rhs Mat-Vec mul
    exact dotProduct challenge_vec intermediate_fn -- vec-vec dot product

/-- **From Lemma 4.9**: Matrix-vector multiplication form of iterated fold :
For a local `steps > 0`, `∀ i ∈ {0, ..., l-steps}`, `y ∈ S^(i+steps)`,
`fold(f^(i), r_0, ..., r_{steps-1})(y) = [⨂_{j=0}^{steps-1}(1-r_j, r_j)] • M_{steps, y}`
`• [f^(i)(x_0) ... f^(i)(x_{2 ^ steps-1})]^T`,
where
- `M_{steps, y}` is the `steps`-step **foldMatrix** of point `y`.
- the right-hand vector's values `(x_0, ..., x_{2 ^ steps-1})` represent the fiber
`(q^(i+steps-1) ∘ ... ∘ q^(i))⁻¹({y}) ⊂ S^(i)`. -/
def localized_fold_matrix_form (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
  (f : (sDomain 𝔽q β h_ℓ_add_R_rate)
      ⟨i, by exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by
        exact Fin.is_le') (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L)
  (r_challenges : Fin steps → L) : (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨↑i + steps, by omega⟩) → L :=
  fun y =>
    let fiber_eval_mapping := fiberEvaluations 𝔽q β (steps := steps)
        (i := ⟨i, by omega⟩)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) f y
    single_point_localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (h_i_add_steps := h_i_add_steps)
      (r_challenges := r_challenges) (y := y) (fiber_eval_mapping := fiber_eval_mapping)

/-- The (2 x 1) vector `F₂(steps, r, z₀, z₁) = [fold(steps, r, z₀), fold(steps, r, z₁)]`.
This is the right-most vector when decomposing the outer single-step fold of **Lemma 4.9**.
NOTE: `h_F₂_y_eq` in lemma `iterated_fold_eq_matrix_form` below shows it OG form in Lemma 4.9. -/
def fold_eval_fiber₂_vec (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps + 1 ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L) (r_challenges : Fin steps → L) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) (i := ⟨i.val + steps + 1, by omega⟩) → (Fin 2) → L := fun y => by
    -- Can also use fiberEvaluations instead
    let fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i + steps, by omega⟩) (steps := 1)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)
    exact fun rowIdx =>
      let zᵢ := fiberMap rowIdx
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
        (steps := steps)
        (h_i_add_steps := by simp only; omega)
        (f := f) (r_challenges := r_challenges) zᵢ

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Helper #1 for Lemma 4.9**: The vector `F₂(steps, r, y) = `
`MatrixCTensor(steps, r) * blockDiagMatrix(steps, M_z₀, M_z₁) * fiberEvaluations(steps+1, r, y)`.
where `z₀, z₁` are the fiber of `y`, `y` is in `S^(i+steps+1)`). -/
lemma fold_eval_fiber₂_eq_mat_mat_vec_mul (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i + steps + 1 ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L) (r_challenges : Fin steps → L)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + steps + 1, by omega⟩)
    (lemma_4_9_inductive_hypothesis :
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps) (i := ⟨i, by omega⟩)
        (h_i_add_steps := by simp only; omega) (f := f) (r_challenges := r_challenges)
      = (localized_fold_matrix_form 𝔽q β (i := i) (steps := steps) (h_i_add_steps := by omega)
        (f := f) (r_challenges := r_challenges))) :
    let F₂_y := (fold_eval_fiber₂_vec 𝔽q β i steps h_i_add_steps f r_challenges) (y)
    let fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i+steps, by omega⟩) (steps := 1)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)
    let z₀ := fiberMap 0
    let z₁ := fiberMap 1
    let M_z₀ := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (y := z₀)
    let M_z₁ := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (y := z₁)
    let fiber_eval_mapping := fiberEvaluations 𝔽q β (steps := steps + 1)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; simp only; omega) f y
    let decomposed_form := ((challengeTensorExpansionMatrix (n := steps) (r := r_challenges)) *
        (blockDiagMatrix (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (n := steps) (Mz₀ := M_z₀) (Mz₁ := M_z₁)))
          *ᵥ fiber_eval_mapping
    F₂_y = decomposed_form := by
  -- funext (halfIdx : Fin 2)
  dsimp only [fold_eval_fiber₂_vec]
  -- 3. Apply the previous main theorem: iterated_fold_eq_matrix_form
  let h_matrix_form := lemma_4_9_inductive_hypothesis
  -- 4. Rewrite LHS using the matrix form theorem: LHS at halfIdx is `iterated_fold ... z_halfIdx`
  conv_lhs => rw [h_matrix_form] -- now lhs is `localized_fold_matrix_form ... z_halfIdx`
  let fiberVec_y_eq_merge := fiberEvaluations_eq_merge_fiberEvaluations_of_one_step_fiber
    (𝔽q := 𝔽q) (β := β) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
    (h_i_add_steps := by simp only; omega) (f := f) (y := y)
  conv_rhs => rw [fiberVec_y_eq_merge]
  simp only [Fin.isValue, Fin.eta]
  -- LHS is localized_fold_matrix_form ... z_halfIdx
  -- RHS is: (MatrixCTensor * BlockDiagMatrix *v (fiberEval(z₀) ++ fiberEval(z₁))) [halfIdx]
  conv_rhs =>
    rw [←Matrix.mulVec_mulVec] -- group BlockDiagMatrix with fiberEval(z₀) ++ fiberEval(z₁)
    rw [←blockDiagMatrix_mulVec_F₂_eq_Fin_merge_PO2] -- distribute the mat-vec multiplication
    rw [←challengeTensorExpansionMatrix_mulVec_F₂_eq_Fin_merge_PO2] -- distribute again
  --  Now both sides are `(Fin 2) → L`
  funext (halfIdx : Fin 2)
  conv_lhs => unfold localized_fold_matrix_form single_point_localized_fold_matrix_form
  conv_rhs => unfold mergeFinMap_PO2_left_right
  by_cases hi : halfIdx.val < 2 ^ 0
  · simp only [reduceAdd, reducePow, pow_zero, lt_one_iff, Fin.val_eq_zero_iff, Fin.isValue,
    Nat.pow_zero, mulVec_mulVec]
    -- first row of F₂_y (LHS): fold(steps, r_challenges, z₀)
    have h_halfIdx_eq_0 : halfIdx = 0 := by omega
    simp only [h_halfIdx_eq_0, Fin.isValue, ↓reduceDIte, Fin.coe_ofNat_eq_mod, zero_mod,
      Fin.zero_eta]
    conv_lhs => rw [Matrix.dotProduct_mulVec]
    conv_rhs => rw [Matrix.mulVec]
    -- Both sides have form (... ⬝ᵥ (fiberEvaluations (z₀)))
    rfl
  · simp only [reduceAdd, reducePow, pow_zero, lt_one_iff, Fin.val_eq_zero_iff, Fin.isValue,
    Nat.pow_zero, mulVec_mulVec]
    -- second row of F₂_y (RHS): fold(steps, r_challenges, z₁)
    have h_halfIdx_eq_1 : halfIdx = 1 := by omega
    simp only [h_halfIdx_eq_1, Fin.isValue, one_ne_zero, ↓reduceDIte, Fin.coe_ofNat_eq_mod,
      mod_succ, tsub_self, Fin.zero_eta]
    conv_lhs => rw [Matrix.dotProduct_mulVec]
    conv_rhs => rw [Matrix.mulVec]
    -- Both sides have form (... ⬝ᵥ (fiberEvaluations (z₁)))
    rfl

omit [NeZero r] [Fintype L] [DecidableEq L] [CharP L 2] [NeZero ℓ] [NeZero 𝓡] in
/-- **Helper #2 for Lemma 4.9**: the (middle) interchangibility transformation in the Lemma 4.9
`butterflyMstrix(0, z₀, z₁) * MatrixCTensor(n, r)`
`= MatrixCTensor(n, r) * butterflyMatrix(n, z₀, z₁)`. Both have size `2 x (2^(n + 1))` -/
lemma butterflyMatrix0_mul_matrixCTensor_eq_matrixCTensor_mul_butterflyMatrix (n : ℕ)
    (z₀ z₁ : L) (r_challenges : Fin n → L) :
    (butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := 0) z₀ z₁) *
      (challengeTensorExpansionMatrix (n := n) (r := r_challenges))
    = (challengeTensorExpansionMatrix (n := n) (r := r_challenges)) *
      (butterflyMatrix (𝓡 := 𝓡) (ℓ := ℓ) (r := r) (n := n) z₀ z₁) := by
  unfold butterflyMatrix challengeTensorExpansionMatrix reindexSquareMatrix
  simp only
  conv_lhs => -- clear way for Matrix.reindex_mul_reindex in lhs
    simp only [reduceAdd, reducePow, Nat.pow_zero, finCongr_refl, neg_smul, one_smul,
    Equiv.refl_symm, Equiv.coe_refl, submatrix_id_id, finCongr_symm]
  conv_lhs => rw [Matrix.reindex_mul_reindex]; rw [Matrix.from4Blocks_mul_from4Blocks]
  conv_rhs => rw [Matrix.reindex_mul_reindex]; rw [Matrix.from4Blocks_mul_from4Blocks]
  simp only [reduceAdd, reducePow, smul_mul, Nat.pow_zero, Matrix.one_mul, smul_of, Matrix.mul_zero,
    add_zero, Matrix.neg_mul, neg_of, zero_add, reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
    finCongr_symm, finCongr_refl, Matrix.mul_smul, Matrix.mul_one, neg_smul, one_smul,
    Matrix.mul_neg, neg_zero, smul_zero]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Lemma 4.9.** The iterated fold equals the localized fold evaluation via matmul form -/
theorem iterated_fold_eq_matrix_form (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (f : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L)
    (r_challenges : Fin steps → L) :
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (steps := steps)
      (i := ⟨i, by omega⟩)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f
      r_challenges =
    localized_fold_matrix_form 𝔽q β i (steps := steps) (h_i_add_steps := h_i_add_steps) f
      r_challenges := by
  induction steps with
  | zero => -- Base Case: steps = 0
    unfold iterated_fold localized_fold_matrix_form single_point_localized_fold_matrix_form
    simp only [Nat.add_zero, Fin.dfoldl, reduceAdd, Fin.val_succ, id_eq, Fin.dfoldlM_zero,
      Fin.isValue, Fin.coe_ofNat_eq_mod, reduceMod, Nat.pow_zero]
    -- The fold loop is empty, returns f(y)
    unfold challengeTensorExpansion foldMatrix fiberEvaluations qMap_total_fiber
    simp only [pure, Nat.pow_zero, ↓reduceDIte, Nat.add_zero, eq_mp_eq_cast, cast_eq, one_mulVec]
    unfold dotProduct
    simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, multilinearWeight, univ_eq_empty,
      Nat.pow_zero, Fin.val_eq_zero, zero_testBit, Bool.false_eq_true, ↓reduceIte, prod_empty,
      one_mul, sum_const, card_singleton, one_smul]
  | succ n ih =>
    -- Inductive Step: steps = n + 1
    -- 1. Unfold the definition of iterated_fold for n+1 steps.
    --    iterated_fold (n+1) is `fold` applied to `iterated_fold n`.
    rw [iterated_fold_last]
    simp only
    -- Let `prev_fold` be the result of folding n times.
    set prev_fold_fn := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) (steps := n) (h_i_add_steps := by
        simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (f := f)
      (r_challenges := Fin.init r_challenges)
    funext (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + n + 1, by omega⟩)
    -- ⊢ fold 𝔽q β ⟨↑i + n, ⋯⟩ ⋯ prev_fold_fn (r_challenges (Fin.last n)) y =
    -- localized_fold_matrix_form 𝔽q β i (n + 1) h_i_add_steps f r_challenges y
    set F₂_y := fold_eval_fiber₂_vec 𝔽q β i (steps := n) h_i_add_steps f
      (r_challenges := Fin.init r_challenges)

    have h_F₂_y_eq : ∀ yPoint, fiberEvaluations 𝔽q β (i := ⟨i.val + n, by omega⟩) (steps := 1)
      (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
      (f := prev_fold_fn) yPoint = F₂_y yPoint := fun yPoint => by rfl

    conv_lhs => -- use vec-matrix-vec form for the outer (single-step) fold()
      rw [fold_eval_single_matrix_mul_form 𝔽q β (i := ⟨i.val + n, by omega⟩)
        (h_i_add_steps := by omega)]; unfold fold_single_matrix_mul_form; simp only
      -- change the right-most multiplier term into F₂_y repr
      rw [h_F₂_y_eq]
      -- Now lhs has this form:` ((CTensor n=1)* butterflyMatrix(0, z₀(y), z₁(y))) * (F₂_y y)`,
        -- => we use **Helper #1** to expand the last term `F₂_y y` into product of 3 terms
      unfold F₂_y
      simp only;
      rw [fold_eval_fiber₂_eq_mat_mat_vec_mul (lemma_4_9_inductive_hypothesis := by
        let res := ih (h_i_add_steps := by omega) (f := f) (r_challenges := Fin.init r_challenges)
        exact res
      )]
      -- Now LHS has this 5-term form: `(CTensor vec n=1) ⬝ᵥ butterflyMatrix(0, z₀(y), z₁(y))`
        -- `*ᵥ [ [ (MatrixCTensor n=n (Fin.init r_challenges)) * (blockDiagMatrix n Mz₀ Mz₁) ]`
              -- `*ᵥ (fiberEvaluations y)                                                    ] ]`
      -- Next, we group term 2 & 3
      rw [←Matrix.mulVec_mulVec] -- group term (4 * 5), split term 3
      rw [Matrix.mulVec_mulVec] -- group term (2 & 3)
      -- => Now we have 3 groups : (1) ⬝ᵥ (2 * 3) *ᵥ (4 *ᵥ 5)
      -- => We apply **Helper #2** to `swap positions of term 2 & 3`
      simp only;
      rw [butterflyMatrix0_mul_matrixCTensor_eq_matrixCTensor_mul_butterflyMatrix] -- Helper #2
      -- Now LHS has 5-term form: `(CTensor vec n=1) ⬝ᵥ (MatrixCTensor n=n (Fin.init r_challenges))`
        -- `butterflyMatrix(n := N, z₀(y), z₁(y)) * (blockDiagMatrix n Mz₀ Mz₁) ]`
          -- `*ᵥ (fiberEvaluations y)`
          -- where `Mz₀` and `Mz₁` are `n-step` foldMatrix of `z₀` and `z₁` respectively
    -- Now the last TWO jobs are to group * transform (term 1 & term 2), (term 3 & term 4)
    set multilinearWeight1step : (Fin 2 → L) := -- This is term 1 in the LHS
      (challengeTensorExpansion 1 fun x ↦ r_challenges (Fin.last n))
    have h_MLNWeight1step_eq: multilinearWeight1step
      = ![1 - r_challenges (Fin.last n), r_challenges (Fin.last n)] := by
        apply challengeTensorExpansion_one
    let h_merge_term1_term2_tensorExpand_for_n_plus_1 :=
      challengeTensorExpansion_decompose_succ (L := L) (n := n) (r := r_challenges)
    conv_lhs => -- JOB 1: group & transform (term 1 & term 2)
      -- => We need to convert `(CTensor 1) ⬝ᵥ (MatrixCTensor n)` into `(CTensor (n + 1))`
      rw [h_MLNWeight1step_eq]
      rw [←Matrix.mulVec_mulVec] -- group (term 3 4 5), split term 2
      rw [Matrix.dotProduct_mulVec] -- group (term 1 & term 2)
      rw [←h_merge_term1_term2_tensorExpand_for_n_plus_1] -- MERGING here
    conv_lhs => -- JOB 2: group & transform (term 3 & term 4), old term indices before JOB 1
      -- => We need to convert `butterflyMatrix(n := N, z₀(y), z₁(y)) * (blockDiagMatrix n Mz₀ Mz₁)`
        -- into `foldMatrix(n := n + 1, y)`
      rw [Matrix.mulVec_mulVec] -- group term (3 * 4)
      -- => We don't really have to do anything, cuz (term 3 * term 4) is
        -- definitionally equal to fold(n + 1, y)
    rfl

def polyToOracleFunc (i : Fin (ℓ + 1)) (P : L[X]) :
  OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) :=
    fun y => P.eval y.val

omit [CharP L 2] [NeZero ℓ] in
/-- **Lemma 4.13** : if f⁽ⁱ⁾ is evaluation of P⁽ⁱ⁾(X) over S⁽ⁱ⁾, then fold(f⁽ⁱ⁾, r_chal)
  is evaluation of P⁽ⁱ⁺¹⁾(X) over S⁽ⁱ⁺¹⁾. At level `i = ℓ`, we have P⁽ˡ⁾ = c
-/
theorem fold_advances_evaluation_poly
  (i : Fin (ℓ)) (h_i_succ_lt : i + 1 < ℓ + 𝓡)
  (coeffs : Fin (2 ^ (ℓ - ↑i)) → L) (r_chal : L) : -- novel coeffs
  let P_i : L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by
    exact Nat.lt_trans (n := i) (k := ℓ+1) (m := ℓ) (h₁ := i.isLt) (by exact Nat.lt_add_one ℓ)
  ⟩) coeffs
  let f_i := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (P := P_i)
  let f_i_plus_1 := fold (i := ⟨i, by omega⟩) (h_i := by omega) (f := f_i) (r_chal := r_chal)
  let new_coeffs := fun j : Fin (2^(ℓ - (i + 1))) =>
    (1 - r_chal) * (coeffs ⟨j.val * 2, by
      rw [←Nat.add_zero (j.val * 2)]
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
        (i := 0) (by omega) (by omega)
    ⟩) +
    r_chal * (coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
        (i := 1) (by omega) (by omega)
    ⟩)
  let P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i+1, by omega⟩) new_coeffs
  f_i_plus_1 = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i+1, by omega⟩) (P := P_i_plus_1) := by
  simp only
  funext y
  set fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := 1)
    (h_i_add_steps := by simp only; omega) (y := y)
  set x₀ := fiberMap 0
  set x₁ := fiberMap 1
  set P_i := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) coeffs
  set new_coeffs := fun j : Fin (2^(ℓ - (i + 1))) =>
    (1 - r_chal) * (coeffs ⟨j.val * 2, by
      have h : j.val * 2 < 2^(ℓ - (i + 1)) * 2 := by omega
      have h2 : 2^(ℓ - i) = 2^(ℓ - (i + 1)) * 2 := by
        conv_rhs => enter[2]; rw [←Nat.pow_one 2]
        rw [←pow_add]; congr
        rw [Nat.sub_add_eq_sub_sub_rev (h1 := by omega) (h2 := by omega)]
        -- ⊢ ℓ - ↑i = ℓ - (↑i + 1 - 1)
        rw [Nat.add_sub_cancel (n := i) (m := 1)]
      omega
    ⟩) +
    r_chal * (coeffs ⟨j.val * 2 + 1, by
      apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1)) (i := 1)
      · omega
      · omega
    ⟩)
  have h_eval_qMap_x₀ : (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval x₀.val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i (by omega) x₀
    simp only [Subtype.eq_iff] at h
    rw [h.symm]
    have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) (by omega)
      (x := x₀) (y := y).mpr (by rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    rw [h_res]
    -- exact qMap_eval_fiber_eq_self ⟦L⟧ ⟨i + 1, by omega⟩ (by simp only; omega) h_i_succ_lt y 0
  have h_eval_qMap_x₁ : (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval x₁.val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i (by omega) x₁
    simp only [Subtype.eq_iff] at h
    rw [h.symm]
    have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) (by omega)
      (x := x₁) (y := y).mpr (by rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
    rw [h_res]
  have hx₀ := qMap_total_fiber_basis_sum_repr 𝔽q β i (steps := 1)
    (h_i_add_steps := by omega) y 0
  have hx₁ := qMap_total_fiber_basis_sum_repr 𝔽q β i (steps := 1)
    (h_i_add_steps := by omega) y 1
  simp only [Fin.isValue] at hx₀ hx₁

  have h_fiber_diff : x₁.val - x₀.val = 1 := by
    simp only [Fin.isValue, x₁, x₀, fiberMap]
    rw [hx₁, hx₀]
    simp only [Fin.isValue, AddSubmonoidClass.coe_finset_sum, SetLike.val_smul]
    have h_index : ℓ + 𝓡 - i = (ℓ + 𝓡 - (i.val + 1)) + 1 := by omega
    rw! (castMode := .all) [h_index]
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] -- (free_term + y_repr) - (free_term + y_repr) = 1
    -- First, simplify the free terms
    simp only [fiber_coeff, eqRec_eq_cast, lt_one_iff, reducePow, Fin.isValue,
      Fin.coe_ofNat_eq_mod, mod_succ, dite_smul, ite_smul, zero_smul, one_smul, zero_mod]
    have h_cast_0 :
        (cast (Eq.symm h_index ▸ rfl : Fin (ℓ + 𝓡 - (↑i + 1) + 1) = Fin (ℓ + 𝓡 - ↑i)) 0).val =
        0 := by
      rw [←Fin.cast_eq_cast (h := by omega)]
      rw [Fin.cast_val_eq_val (h_eq := by omega)]
      simp only [Fin.coe_ofNat_eq_mod, mod_succ_eq_iff_lt, succ_eq_add_one, lt_add_iff_pos_left]
      omega
    have h_cast_1 :
        (cast (Eq.symm h_index ▸ rfl : Fin (ℓ + 𝓡 - (↑i + 1) + 1) = Fin (ℓ + 𝓡 - ↑i)) 1).val =
        1 := by
      rw [←Fin.cast_eq_cast (h := by omega)]
      rw [Fin.cast_val_eq_val (h_eq := by omega)]
      simp only [Fin.coe_ofNat_eq_mod, mod_succ_eq_iff_lt, succ_eq_add_one,
        lt_add_iff_pos_left, tsub_pos_iff_lt]
      omega
    simp only [h_cast_0, ↓reduceDIte]
    have h_getBit_0_of_0 : Nat.getBit (k := 0) (n := 0) = 0 := by
      simp only [getBit, shiftRight_zero, and_one_is_mod, zero_mod]
    have h_getBit_0_of_1 : Nat.getBit (k := 0) (n := 1) = 1 := by
      simp only [getBit, shiftRight_zero, Nat.and_self]
    simp only [h_getBit_0_of_1, one_ne_zero, ↓reduceIte, h_getBit_0_of_0, zero_add]
    rw! (castMode := .all) [←h_index]
    rw [cast_eq]
    simp only [get_sDomain_basis, Fin.coe_ofNat_eq_mod, zero_mod, add_zero, cast_eq]
    rw [normalizedWᵢ_eval_βᵢ_eq_1 𝔽q β]
    ring_nf
    conv_rhs => rw [←add_zero (a := 1)]
    congr 1
    rw [sub_eq_zero]
    apply Finset.sum_congr (h := by rfl)
    simp only [mem_univ, congr_eqRec, Fin.val_succ, Nat.add_eq_zero, one_ne_zero, and_false,
      ↓reduceDIte, add_tsub_cancel_right, Fin.eta, imp_self, implies_true]
  set P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i+1, by omega⟩) new_coeffs
  -- Set up the even and odd refinement polynomials
  set P₀_coeffs := fun j : Fin (2^(ℓ - (i + 1))) => coeffs ⟨j.val * 2, by
    have h1 : ℓ - (i + 1) + 1 = ℓ - i := by omega
    have h2 : 2^(ℓ - (i + 1) + 1) = 2^(ℓ - i) := by rw [h1]
    have h3 : 2^(ℓ - (i + 1)) * 2 = 2^(ℓ - (i + 1) + 1) := by rw [pow_succ]
    rw [← h2, ← h3]; omega⟩
  set P₁_coeffs := fun j : Fin (2^(ℓ - (i + 1))) => coeffs ⟨j.val * 2 + 1, by
    have h1 : ℓ - (i + 1) + 1 = ℓ - i := by omega
    have h2 : 2^(ℓ - (i + 1) + 1) = 2^(ℓ - i) := by rw [h1]
    have h3 : 2^(ℓ - (i + 1)) * 2 = 2^(ℓ - (i + 1) + 1) := by rw [pow_succ]
    rw [← h2, ← h3]; omega⟩
  set P₀ := evenRefinement 𝔽q β h_ℓ_add_R_rate i coeffs
  set P₁ := oddRefinement 𝔽q β h_ℓ_add_R_rate i coeffs
  have h_P_i_eval := evaluation_poly_split_identity 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ coeffs
  -- Equation 39 : P^(i)(X) = P₀^(i+1)(q^(i)(X)) + X · P₁^(i+1)(q^(i)(X))
  have h_equation_39_x₀ : P_i.eval x₀.val = P₀.eval y.val + x₀.val * P₁.eval y.val := by
    simp only [h_P_i_eval, Fin.eta, Polynomial.eval_add, eval_comp,
      h_eval_qMap_x₀, Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  have h_equation_39_x₁ : P_i.eval x₁.val = P₀.eval y.val + x₁.val * P₁.eval y.val := by
    simp only [h_P_i_eval, Fin.eta, Polynomial.eval_add, eval_comp,
      h_eval_qMap_x₁, Polynomial.eval_mul, Polynomial.eval_X, P_i, P₀, P₁]
  set f_i := fun (x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩) => P_i.eval (x.val : L)
  set f_i_plus_1 := fold (i := ⟨i, by omega⟩) (h_i := by omega) (f := f_i) (r_chal := r_chal)
  -- Unfold the definition of f_i_plus_1 using the fold function
  have h_fold_def : f_i_plus_1 y =
      f_i x₀ * ((1 - r_chal) * x₁.val - r_chal) +
      f_i x₁ * (r_chal - (1 - r_chal) * x₀.val) := rfl
  -- Main calculation following the outline
  calc f_i_plus_1 y
    = f_i x₀ * ((1 - r_chal) * x₁.val - r_chal) +
        f_i x₁ * (r_chal - (1 - r_chal) * x₀.val) := h_fold_def
    _ = P_i.eval x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
        P_i.eval x₁.val * (r_chal - (1 - r_chal) * x₀.val) := by simp only [f_i]
    _ = (P₀.eval y.val + x₀.val * P₁.eval y.val) * ((1 - r_chal) * x₁.val - r_chal) +
        (P₀.eval y.val + x₁.val * P₁.eval y.val) * (r_chal - (1 - r_chal) * x₀.val) := by
      rw [h_equation_39_x₀, h_equation_39_x₁]
    _ = P₀.eval y.val * ((1 - r_chal) * x₁.val - r_chal + r_chal - (1 - r_chal) * x₀.val) +
        P₁.eval y.val * (x₀.val * ((1 - r_chal) * x₁.val - r_chal) +
          x₁.val * (r_chal - (1 - r_chal) * x₀.val)) := by ring
    _ = P₀.eval y.val * ((1 - r_chal) * (x₁.val - x₀.val)) +
        P₁.eval y.val * ((x₁.val - x₀.val) * r_chal) := by ring
    _ = P₀.eval y.val * (1 - r_chal) + P₁.eval y.val * r_chal := by rw [h_fiber_diff]; ring
    _ = P_i_plus_1.eval y.val := by
      simp only [P_i_plus_1, P₀, P₁, new_coeffs, evenRefinement, oddRefinement,
        intermediateEvaluationPoly]
      conv_lhs => enter [1]; rw [mul_comm, ←Polynomial.eval_C_mul]
      conv_lhs => enter [2]; rw [mul_comm, ←Polynomial.eval_C_mul]
      -- ⊢ eval y (C (1-r) * ∑...) + eval y (C r * ∑...) = eval y (∑...)
      rw [←Polynomial.eval_add]
      -- ⊢ poly_left.eval y = poly_right.eval y
      congr
      simp_rw [mul_sum, ←Finset.sum_add_distrib]
      -- We now prove that the terms inside the sums are equal for each index.
      apply Finset.sum_congr rfl
      intro j hj
      have h_j_lt : j.val < 2 ^ (ℓ - (↑i + 1)) := by
        rw [Nat.sub_add_eq]
        omega
      conv_lhs => enter [1]; rw [mul_comm (a := Polynomial.C (coeffs ⟨j.val * 2, by
        rw [←Nat.add_zero (j.val * 2)]
        apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
          (i := 0) (by omega) (by omega)⟩)), ←mul_assoc,
        mul_comm (a := Polynomial.C (1 - r_chal))]; rw [mul_assoc]
      conv_lhs => enter [2]; rw [mul_comm (a := Polynomial.C (coeffs ⟨j.val * 2 + 1, by
        apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
          (i := 1) (by omega) (by omega)⟩)), ←mul_assoc,
        mul_comm (a := Polynomial.C r_chal)]; rw [mul_assoc]
      conv_rhs => rw [mul_comm]
      rw [←mul_add]
      congr
      simp only [←Polynomial.C_mul, ←Polynomial.C_add]

/-- Helper: Bound proof for the indices -/
lemma index_bound_check {ℓ i steps : ℕ} (j m : ℕ)
    (hj : j < 2 ^ (ℓ - (i + steps))) (hm : m < 2 ^ steps) (h_le : i + steps ≤ ℓ) :
    j * 2 ^ steps + m < 2 ^ (ℓ - i) := by
  -- Arithmetic proof: j * 2^s + m < (j+1) * 2^s <= 2^(L-i-s) * 2^s = 2^(L-i)
  calc
    j * 2 ^ steps + m
    _ < j * 2 ^ steps + 2 ^ steps := by apply Nat.add_lt_add_left hm
    _ = (j + 1) * 2 ^ steps := by ring
    _ ≤ (2 ^ (ℓ - (i + steps))) * 2 ^ steps := by
      apply Nat.mul_le_mul_right
      exact hj
    _ = 2 ^ (ℓ - i - steps + steps) := by
      rw [←Nat.pow_add]; simp only [ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
        pow_right_inj₀, Nat.add_right_cancel_iff]; omega
    _ = 2 ^ (ℓ - i) := by
      congr 1
      rw [Nat.sub_add_cancel]
      -- Proof that steps ≤ ℓ - i
      apply Nat.le_sub_of_add_le
      omega

omit [CharP L 2] [NeZero ℓ] in
/-- **Lemma 4.13 Generalization** : if f⁽ⁱ⁾ is evaluation of P⁽ⁱ⁾(X) over S⁽ⁱ⁾,
then fold(f⁽ⁱ⁾, r_chal) is evaluation of P⁽ⁱ⁺¹⁾(X) over S⁽ⁱ⁺¹⁾.
At level `i = ℓ`, we have P⁽ˡ⁾ = c (constant polynomial).
-/
theorem iterated_fold_advances_evaluation_poly
  (i : Fin (ℓ)) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
  (coeffs : Fin (2 ^ (ℓ - ↑i)) → L) (r_challenges : Fin steps → L) : -- novel coeffs
  let P_i : L[X] := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by
    exact Nat.lt_trans (n := i) (k := ℓ+1) (m := ℓ) (h₁ := i.isLt) (by exact Nat.lt_add_one ℓ)
  ⟩) coeffs
  let f_i := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (P := P_i)
  let f_i_plus_steps := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
    (steps := steps) (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega)
      (f := f_i) (r_challenges := r_challenges)
  let new_coeffs := fun j : Fin (2^(ℓ - (i + steps))) =>
    ∑ m : Fin (2 ^ steps),
      multilinearWeight (r := r_challenges) (i := m) * coeffs ⟨j.val * 2 ^ steps + m.val, by
        apply index_bound_check j.val m.val j.isLt m.isLt h_i_add_steps⟩
  let P_i_plus_steps :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i+steps, by omega⟩) new_coeffs
  f_i_plus_steps = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i+steps, by omega⟩) (P := P_i_plus_steps) := by
-- Induction on steps
  induction steps generalizing i with
  | zero =>
    -- Base Case: 0 Steps
    dsimp only [Nat.add_zero, iterated_fold, reduceAdd, Fin.val_succ, Lean.Elab.WF.paramLet, id_eq,
      Fin.dfoldl_zero, Nat.pow_zero, multilinearWeight, Fin.val_eq_zero, zero_testBit,
      Bool.false_eq_true]
    funext y -- Sum over Fin 1 (j=0)
    simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, univ_eq_empty, Fin.val_eq_zero,
      zero_testBit, Bool.false_eq_true, ↓reduceIte, prod_empty, mul_one, add_zero, Fin.eta, one_mul,
      sum_const, card_singleton, one_smul]
  | succ s ih =>
    simp only
    funext y
    -- 1. Unfold Fold (LHS)
    -- iterated_fold (s+1) = fold (iterated_fold s)
    rw [iterated_fold_last]
    set P_i := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) coeffs
    set f_i := polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (P := P_i)
    set f_i_plus_steps := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (steps := s + 1) (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (f := f_i) (r_challenges := r_challenges)
    -- 2. Setup Inductive Step
    let r_s := Fin.init r_challenges
    let r_last := r_challenges (Fin.last s)
    -- Apply IH to the first s steps
    -- We need to construct the coefficients for step s
    let coeffs_s := fun j : Fin (2^(ℓ - (i + s))) =>
      ∑ m : Fin (2 ^ s),
        multilinearWeight (r := r_s) (i := m) * coeffs ⟨j.val * 2 ^ s + m.val, by
          apply index_bound_check j.val m.val j.isLt m.isLt (by omega)
        ⟩
    let f_folded_s_steps := (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := s) (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (f := f_i) (r_challenges := r_s))
    let poly_eval_folded_s_steps :=
      polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + s, by omega⟩) (P := intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨↑i + s, by omega⟩ coeffs_s)
    have h_eval_s : f_folded_s_steps = poly_eval_folded_s_steps := by
      unfold f_folded_s_steps poly_eval_folded_s_steps
      rw [ih (i := i)]
      omega
    unfold f_folded_s_steps at h_eval_s
    conv_lhs =>
      simp only
      rw [h_eval_s]
    -- 3. Apply Single Step Lemma
    -- fold(P_s, r_last) -> P_{s+1}
    -- The lemma fold_advances_evaluation_poly tells us the coefficients transform as:
    -- C_new[j] = (1 - r) * C_s[2j] + r * C_s[2j+1]
    let fold_advances_evaluation_poly_res := fold_advances_evaluation_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i+s, by omega⟩) (h_i_succ_lt := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (coeffs := coeffs_s) (r_chal := r_last)
    simp only [r_last] at fold_advances_evaluation_poly_res
    unfold poly_eval_folded_s_steps
    conv_lhs => rw [fold_advances_evaluation_poly_res]
    --   ⊢ Polynomial.eval y ... = Polynomial.eval y ...
    congr 1
    congr 1
    funext (j : Fin (2 ^ (ℓ - (↑i + s + 1))))
    unfold coeffs_s
    simp only
    have h_two_pow_s_succ_eq: 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by omega
    conv_rhs =>
      rw! (castMode := .all) [h_two_pow_s_succ_eq]
      rw [Fin.sum_univ_add]
      simp only [eqRec_eq_cast]
      rw [←Fin.cast_eq_cast (h := by omega)]
      simp only [Fin.coe_castAdd, Fin.natAdd_eq_addNat, Fin.coe_addNat]
      unfold Fin.addNat
    -- ∑ + ∑ = ∑ + ∑
    congr 1
    · conv_lhs => rw [mul_sum]
      congr 1
      funext (x : Fin (2 ^ s))
      conv_lhs => rw [←mul_assoc]
      congr 1
      · rw [multilinearWeight_succ_lower_half (h_lt := by simp only [Fin.coe_cast, Fin.coe_castAdd,
          Fin.is_lt])]
        rw [mul_comm]; rfl
      · simp_rw [←two_mul (n := 2 ^ s), ←mul_assoc]
    · conv_lhs => rw [mul_sum]
      congr 1
      funext (x : Fin (2 ^ s))
      conv_lhs => rw [←mul_assoc]
      congr 1
      · rw [multilinearWeight_succ_upper_half (r := r_challenges) (j := x)
          (h_eq := by simp only [Fin.cast_mk]), mul_comm]
      · congr 1
        congr 1
        conv_lhs => rw [add_mul, one_mul, add_assoc]
        conv_rhs => rw [←two_mul (n := 2 ^ s), ←mul_assoc]
        omega

/-- Given a point `v ∈ S^(0)`, extract the middle `steps` bits `{v_i, ..., v_{i+steps-1}}`
as a `Fin (2 ^ steps)`. -/
def extractMiddleFinMask (v : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨0, by exact pos_of_neZero r⟩)
    (i : Fin ℓ) (steps : ℕ) : Fin (2 ^ steps) := by
  let vToFin := AdditiveNTT.sDomainToFin 𝔽q β h_ℓ_add_R_rate ⟨0, by
    exact pos_of_neZero r⟩ (by simp only [add_pos_iff]; left; exact pos_of_neZero ℓ) v
  simp only [tsub_zero] at vToFin
  let middleBits := Nat.getMiddleBits (offset := i.val) (len := steps) (n := vToFin.val)
  exact ⟨middleBits, Nat.getMiddleBits_lt_two_pow⟩

/-- The equality polynomial eq̃(r, r') that evaluates to 1 when r = r' and 0 otherwise.
This is used in the final sumcheck identity : s_ℓ = c · eq̃(r, r') -/
def eqTilde {L : Type} [CommRing L] {ℓ : ℕ} (r r' : Fin ℓ → L) : L :=
  MvPolynomial.eval r' (MvPolynomial.eqPolynomial r)

end Essentials

section SoundnessTools
-- In this section, we use the generic notation `steps` instead of `ϑ` to avoid conflicts

/-!
### Binary Basefold Specific Code Definitions

Definitions specific to the Binary Basefold protocol based on the fundamentals document.
-/

/-- The Reed-Solomon code C^(i) for round i in Binary Basefold.
For each i ∈ {0, steps, ..., ℓ}, C(i) is the Reed-Solomon code
RS_{L, S⁽ⁱ⁾}[2^{ℓ+R-i}, 2^{ℓ-i}]. -/
def BBF_Code (i : Fin (ℓ + 1)) :
  Submodule L ((sDomain 𝔽q β h_ℓ_add_R_rate)
    ⟨i, by
      exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by omega) (h₂ := by omega)⟩ → L) :=
  let domain : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ ↪ L :=
    ⟨fun x => x.val, fun x y h => by exact Subtype.ext h⟩
  ReedSolomon.code (domain := domain) (deg := 2^(ℓ - i.val))

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
lemma exists_BBF_poly_of_codeword (i : Fin (ℓ + 1))
  (u : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) :
  ∃ P : L⦃<2^(ℓ-i)⦄[X], polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (P := P)
    = u := by
  have h_u_mem := u.property
  unfold BBF_Code at h_u_mem
  simp only [code, evalOnPoints, Embedding.coeFn_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.mem_map] at h_u_mem
  -- We use the same logic you had, but we return the Subtype explicitly
  obtain ⟨P_raw, hP_raw⟩ := h_u_mem
  -- Construct the subtype element
  let P : L⦃<2^(ℓ-i)⦄[X] := ⟨P_raw, hP_raw.1⟩
  use P
  -- Prove the evaluation part
  exact hP_raw.2

def getBBF_Codeword_poly (i : Fin (ℓ + 1))
  (u : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) : L⦃<2^(ℓ-i)⦄[X] :=
  Classical.choose (exists_BBF_poly_of_codeword 𝔽q β i u)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
lemma getBBF_Codeword_poly_spec (i : Fin (ℓ + 1))
  (u : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) :
  u = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (P := getBBF_Codeword_poly 𝔽q β i u) := by
  let res := Classical.choose_spec (exists_BBF_poly_of_codeword 𝔽q β i u)
  exact id (Eq.symm res)

def getBBF_Codeword_of_poly (i : Fin (ℓ + 1)) (P : L⦃< 2 ^ (ℓ - i)⦄[X]) :
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  let g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i :=
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (P := P)
  have h_g_mem : g ∈ BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
    unfold BBF_Code
    simp only [code, evalOnPoints, Embedding.coeFn_mk, LinearMap.coe_mk,
      AddHom.coe_mk, Submodule.mem_map]
    use P
    constructor
    · simp only [SetLike.coe_mem]
    · funext y
      exact rfl
  exact ⟨g, h_g_mem⟩

/-- The (minimum) distance d_i of the code C^(i) : `dᵢ := 2^(ℓ + R - i) - 2^(ℓ - i) + 1` -/
abbrev BBF_CodeDistance (i : Fin (ℓ + 1)) : ℕ :=
  ‖((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L))‖₀

omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
lemma BBF_CodeDistance_eq (i : Fin (ℓ + 1)) :
  BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    = 2^(ℓ + 𝓡 - i.val) - 2^(ℓ - i.val) + 1 := by
  unfold BBF_CodeDistance
  -- Create the embedding from domain elements to L
  let domain : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ ↪ L :=
    ⟨fun x => x.val, fun x y h => by exact Subtype.ext h⟩
  -- Create α : Fin m → L by composing with an equivalence
  let m := Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩)
  have h_dist_RS := ReedSolomonCode.dist_eq' (F := L) (ι := (sDomain 𝔽q β h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩)) (α := domain) (n := 2^(ℓ - i.val)) (h := by
      rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by
        simp only; apply Nat.lt_add_of_pos_right_of_le; omega)];
      rw [hF₂.out];
      simp only; apply Nat.pow_le_pow_right (hx := by omega);
      omega
    )
  unfold BBF_Code
  rw [h_dist_RS]
  rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := by
    simp only; apply Nat.lt_add_of_pos_right_of_le; omega), hF₂.out]

/-- Disagreement set Δ : The set of points where two functions disagree.
For functions f^(i) and g^(i), this is {y ∈ S^(i) | f^(i)(y) ≠ g^(i)(y)}. -/
def disagreementSet (i : Fin (ℓ + 1))
  (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
  Finset ((sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩) := {y | f y ≠ g y}

/-- Fiber-wise disagreement set Δ^(i) : The set of points y ∈ S^(i+ϑ) for which
functions f^(i) and g^(i) are not identical when restricted to the entire fiber
of points in S⁽ⁱ⁾ that maps to y. -/
def fiberwiseDisagreementSet (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i.val + steps ≤ ℓ) (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate :=
      h_ℓ_add_R_rate) ⟨i, by omega⟩) :
  Finset ((sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + steps, by omega⟩) :=
  -- The set of points `y ∈ S^{i+steps}` that there exists a
    -- point `x` in its fiber where `f x ≠ g x`
  {y | ∃ x, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i)
    (k := steps) (h_bound := by omega) x = y ∧ f x ≠ g x}

def pair_fiberwiseDistance (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
  (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) : ℕ :=
    (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).card

/-- Fiber-wise distance d^(i) : The minimum size of the fiber-wise disagreement set
between f^(i) and any codeword in C^(i). -/
def fiberwiseDistance (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i.val, by omega⟩) : ℕ :=
  -- The minimum size of the fiber-wise disagreement set between f^(i) and any codeword in C^(i)
  -- d^(i)(f^(i), C^(i)) := min_{g^(i) ∈ C^(i)} |Δ^(i)(f^(i), g^(i))|
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i.val, by omega⟩
  let disagreement_sizes := (fun (g : C_i) =>
    pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps
      (h_i_add_steps := h_i_add_steps) (f := f) (g := g)) '' Set.univ
  sInf disagreement_sizes

/-- Fiberwise closeness : f^(i) is fiberwise close to C^(i) if
2 * d^(i)(f^(i), C^(i)) < d_{i+steps} -/
def fiberwiseClose (i : Fin ℓ) (steps : ℕ) [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩) : Prop :=
  2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps
    (h_i_add_steps := h_i_add_steps) (f := f) <
      (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩) : ℕ∞)

def pair_fiberwiseClose (i : Fin ℓ) (steps : ℕ) [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) : Prop :=
    2 * pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps
      (h_i_add_steps := h_i_add_steps) (f := f) (g := g) <
      (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩) : ℕ∞)

/-- Hamming UDR-closeness : f is close to C in Hamming distance if `2 * d(f, C) < d_i` -/
def UDRClose (i : Fin (ℓ + 1)) (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    : Prop :=
    2 * Δ₀(f, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) <
      BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)

def pair_UDRClose (i : Fin (ℓ + 1))
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  2 * Δ₀(f, g) < BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)

omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
lemma UDRClose_iff_within_UDR_radius (i : Fin (ℓ + 1))
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f ↔
    Δ₀(f, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≤
      uniqueDecodingRadius (ι := (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩))
        (F := L) (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) := by
  unfold UDRClose
  let card_Sᵢ := sDomain_card 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)
    (h_i := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
  conv_rhs =>
    unfold BBF_Code;
    rw [ReedSolomonCode.uniqueDecodingRadius_RS_eq' (h := by
      rw [card_Sᵢ, hF₂.out]; simp only; apply Nat.pow_le_pow_right (hx := by omega); omega
    )];
  simp_rw [card_Sᵢ, hF₂.out, BBF_CodeDistance_eq]
  simp only [cast_add, ENat.coe_sub, cast_pow, cast_ofNat, cast_one]
  constructor

  · intro h_UDRClose
    -- 1. Prove distance is finite
    -- The hypothesis implies 2 * Δ₀ is finite, so Δ₀ must be finite.
    have h_finite : Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≠ ⊤ := by
      intro h_top
      rw [h_top] at h_UDRClose
      exact not_top_lt h_UDRClose
    -- 2. Lift to Nat to use standard arithmetic
    lift Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) to ℕ
      using h_finite with d_nat h_eq
    dsimp only [BBF_Code] at h_eq
    simp_rw [←h_eq]
    -- ⊢ ↑d_nat ≤ ↑((2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i)) / 2)
    have h_lt : 2 * d_nat < 2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) + 1 := by
      norm_cast at h_UDRClose ⊢ -- both h_UDRClose and ⊢ are in ENat
    simp only [Nat.cast_le]
    have h_le := Nat.le_of_lt_succ (m := 2 * d_nat) (n := 2^(ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) ) h_lt
    rw [Nat.mul_comm 2 d_nat] at h_le
    rw [←Nat.le_div_iff_mul_le (k0 := by norm_num)] at h_le
    exact h_le
  · intro h_within
    -- 1. Prove finite
    have h_finite : Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≠ ⊤ := by
      intro h_top
      unfold BBF_Code at h_top
      simp only [h_top, top_le_iff, ENat.coe_ne_top] at h_within

    -- 2. Lift to Nat
    lift Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) to ℕ
      using h_finite with d_nat h_eq

    unfold BBF_Code at h_eq
    rw [←h_eq] at h_within
    norm_cast at h_within ⊢
    -- now both h_within and ⊢ are in ENat, equality can be converted
    omega

/-- Unique closest codeword in the unique decoding radius of a function f -/
@[reducible, simp]
def UDRCodeword (i : Fin (ℓ + 1))
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, i.isLt⟩)
  (h_within_radius : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f) :
  OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, i.isLt⟩
   := by
  let h_ExistsUnique := (Code.UDR_close_iff_exists_unique_close_codeword
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) f).mp (by
    rw [UDRClose_iff_within_UDR_radius] at h_within_radius
    exact h_within_radius
  )
  -- h_ExistsUnique : ∃! v, v ∈ ↑(BBF_Code 𝔽q β i)
    -- ∧ Δ₀(f, v) ≤ Code.uniqueDecodingRadius ↑(BBF_Code 𝔽q β i)
  exact (Classical.choose h_ExistsUnique)

omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
lemma UDRCodeword_mem_BBF_Code (i : Fin (ℓ + 1))
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, i.isLt⟩)
  (h_within_radius : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f) :
  (UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f h_within_radius) ∈
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  unfold UDRCodeword
  simp only [Fin.eta, SetLike.mem_coe, and_imp]
  let h_ExistsUnique := (Code.UDR_close_iff_exists_unique_close_codeword
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) f).mp (by
    rw [UDRClose_iff_within_UDR_radius] at h_within_radius
    exact h_within_radius
  )
  let res := (Classical.choose_spec h_ExistsUnique).1.1
  simp only [SetLike.mem_coe, and_imp] at res
  exact res

omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
lemma dist_to_UDRCodeword_le_uniqueDecodingRadius (i : Fin (ℓ + 1))
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, i.isLt⟩)
  (h_within_radius : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f) :
  Δ₀(f, UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f h_within_radius) ≤
    uniqueDecodingRadius (ι := (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩))
      (F := L) (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  let h_ExistsUnique := (Code.UDR_close_iff_exists_unique_close_codeword
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) f).mp (by
    rw [UDRClose_iff_within_UDR_radius] at h_within_radius
    exact h_within_radius
  ) -- res : ∃! v, v ∈ ↑(BBF_Code 𝔽q β i) ∧ Δ₀(f, v) ≤ uniqueDecodingRadius ↑(BBF_Code 𝔽q β i)
  let res := (Classical.choose_spec h_ExistsUnique).1
  simp only [Fin.eta, SetLike.mem_coe, and_imp] at res
  let h_close := res.2
  unfold UDRCodeword
  simp only [Fin.eta, SetLike.mem_coe, and_imp, ge_iff_le]
  exact h_close

/-- Computational version of `UDRCodeword`, where we use the Berlekamp-Welch decoder to extract
the closest codeword within the unique decoding radius of a function `f` -/
def extractUDRCodeword
  (i : Fin (ℓ + 1)) (h_i : i < ℓ + 𝓡)
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, i.isLt⟩)
  (h_within_radius : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f) :
  OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, i.isLt⟩
   := by
  -- Set up Berlekamp-Welch parameters
  set domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩)
  set d := Δ₀(f, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩))
  let e : ℕ := d.toNat
  have h_dist_ne_top : d ≠ ⊤ := by
    intro h_dist_eq_top
    unfold UDRClose at h_within_radius
    unfold d at h_dist_eq_top
    simp only [h_dist_eq_top, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENat.mul_top,
      not_top_lt] at h_within_radius
  let k : ℕ := 2^(ℓ - i.val)  -- degree bound from BBF_Code definition
  -- Convert domain to Fin format for Berlekamp-Welch
  let domain_to_fin : (sDomain 𝔽q β h_ℓ_add_R_rate)
    ⟨i, by omega⟩ ≃ Fin domain_size := by
    simp only [domain_size]
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (h_i := h_i)]
    have h_equiv := sDomainFinEquiv 𝔽q β
      h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := h_i)
    convert h_equiv
    exact hF₂.out
  -- ωs is the mapping from the point index to the actually point in the domain S^{i}
  let ωs : Fin domain_size → L := fun j => (domain_to_fin.symm j).val
  let f_vals : Fin domain_size → L := fun j => f (domain_to_fin.symm j)
  -- Run Berlekamp-Welch decoder to get P(X) in monomial basis
  have domain_neZero : NeZero domain_size := by
    simp only [domain_size];
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (h_i := h_i)]
    exact {
      out := by
        rw [hF₂.out]
        simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true]
    }
  let berlekamp_welch_result : Option L[X] := BerlekampWelch.decoder (F := L) e k ωs f_vals
  have h_ne_none : berlekamp_welch_result ≠ none := by
    -- 1) Choose a codeword achieving minimal Hamming distance (closest codeword).
    let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
    let S := (fun (g : C_i) => Δ₀(f, g)) '' Set.univ
    let SENat := (fun (g : C_i) => (Δ₀(f, g) : ENat)) '' Set.univ
      -- let S_nat := (fun (g : C_i) => hammingDist f g) '' Set.univ
    have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
    have h_coe_sinfS_eq_sinfSENat : ↑(sInf S) = sInf SENat := by
      rw [ENat.coe_sInf (hs := hS_nonempty)]
      simp only [SENat, Set.image_univ, sInf_range]
      simp only [S, Set.image_univ, iInf_range]
    rcases Nat.sInf_mem hS_nonempty with ⟨g_subtype, hg_subtype, hg_min⟩
    rcases g_subtype with ⟨g_closest, hg_mem⟩
    have h_dist_f : hammingDist f g_closest ≤ e := by
      rw [show e = d.toNat from rfl]
      -- The distance `d` is exactly the Hamming distance of `f` to `g_closest` (lifted to `ℕ∞`).
      have h_dist_eq_hamming : d = (hammingDist f g_closest) := by
        -- We found `g_closest` by taking the `sInf` of all distances, and `hg_min`
        -- shows that the distance to `g_closest` achieves this `sInf`.
        have h_distFromCode_eq_sInf : d = sInf SENat := by
          apply le_antisymm
          · -- Part 1 : `d ≤ sInf ...`
            simp only [d, distFromCode]
            apply sInf_le_sInf
            intro a ha
            -- `a` is in `SENat`, so `a = ↑Δ₀(f, g)` for some codeword `g`.
            rcases (Set.mem_image _ _ _).mp ha with ⟨g, _, rfl⟩
            -- We must show `a` is in the set for `d`, which is `{d' | ∃ v, ↑Δ₀(f, v) ≤ d'}`.
            -- We can use `g` itself as the witness `v`, since `↑Δ₀(f, g) ≤ ↑Δ₀(f, g)`.
            use g; simp only [Fin.eta, Subtype.coe_prop, le_refl, and_self]
          · -- Part 2 : `sInf ... ≤ d`
            simp only [d, distFromCode]
            apply le_sInf
            -- Let `d'` be any element in the set that `d` is the infimum of.
            intro d' h_d'
            -- Unpack `h_d'` : there exists some `v` in the code such that
            -- `↑(hammingDist f v) ≤ d'`.
            rcases h_d' with ⟨v, hv_mem, h_dist_v_le_d'⟩
            -- By definition, `sInf SENat` is a lower bound for all elements in `SENat`.
            -- The element `↑(hammingDist f v)` is in `SENat`.
            have h_sInf_le_dist_v : sInf SENat ≤ ↑(hammingDist f v) := by
              apply sInf_le -- ⊢ ↑Δ₀(f, v) ∈ SENat
              rw [Set.mem_image]
              -- ⊢ ∃ x ∈ Set.univ, ↑Δ₀(f, ↑x) = ↑Δ₀(f, v)
              simp only [Fin.eta, Set.mem_univ, Nat.cast_inj, true_and, Subtype.exists, exists_prop]
              -- ⊢ ∃ a ∈ C_i, Δ₀(f, a) = Δ₀(f, v)
              use v
              exact And.symm ⟨rfl, hv_mem⟩
            -- Now, chain the inequalities : `sInf SENat ≤ ↑(dist_to_any_v) ≤ d'`.
            exact h_sInf_le_dist_v.trans h_dist_v_le_d'
        rw [h_distFromCode_eq_sInf, ←h_coe_sinfS_eq_sinfSENat, ←hg_min]
      rw [h_dist_eq_hamming]
      rw [ENat.toNat_coe]
    -- Get the closest polynomial
    obtain ⟨p, hp_deg_lt : p ∈ L[X]_k, hp_eval⟩ : ∃ p, p ∈ Polynomial.degreeLT L k ∧
      (fun (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)) ↦ p.eval (↑x)) = g_closest := by
      simp only [Fin.eta, BBF_Code, code, evalOnPoints, Function.Embedding.coeFn_mk,
        Submodule.mem_map, LinearMap.coe_mk, AddHom.coe_mk, C_i] at hg_mem
      rcases hg_mem with ⟨p_witness, hp_prop, hp_eq⟩
      use p_witness
    have natDeg_p_lt_k : p.natDegree < k := by
      simp only [mem_degreeLT] at hp_deg_lt
      by_cases hi : i = ℓ
      · simp only [hi, tsub_self, pow_zero, cast_one, lt_one_iff, k] at ⊢ hp_deg_lt
        by_cases hp_p_eq_0 : p = 0
        · rw [hp_p_eq_0, Polynomial.natDegree_zero];
        · rw [Polynomial.natDegree_eq_of_degree_eq_some]
          have h_deg_p : p.degree = 0 := by
            have h_le_zero : p.degree ≤ 0 := by
              exact WithBot.lt_one_iff_le_zero.mp hp_deg_lt
            have h_deg_ne_bot : p.degree ≠ ⊥ := by
              rw [Polynomial.degree_ne_bot]; omega
            apply le_antisymm h_le_zero (zero_le_degree_iff.mpr hp_p_eq_0)
          simp only [h_deg_p, CharP.cast_eq_zero]
      · by_cases hp_p_eq_0 : p = 0
        · rw [hp_p_eq_0, Polynomial.natDegree_zero];
          have h_i_lt_ℓ : i < ℓ := by omega
          simp only [ofNat_pos, pow_pos, k]
        · rw [Polynomial.natDegree_lt_iff_degree_lt (by omega)]
          exact hp_deg_lt
    have h_decoder_succeeds : BerlekampWelch.decoder e k ωs f_vals = some p := by
      apply BerlekampWelch.decoder_eq_some
      · -- ⊢ `2 * e < d_i = n - k + 1`
        have h_le: 2 * e ≤ domain_size - k := by
          have hS_card_eq_domain_size := sDomain_card 𝔽q β (i := ⟨i, by omega⟩) (h_i := by omega)
          simp only [domain_size, k]; simp_rw [hS_card_eq_domain_size, hF₂.out]
          unfold UDRClose at h_within_radius
          rw [BBF_CodeDistance_eq] at h_within_radius
          -- h_within_radius : 2 * Δ₀(f, ↑(BBF_Code 𝔽q β i))
            -- < ↑(2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) + 1)
          dsimp only [Fin.eta, e, d]
          lift Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) to ℕ
            using h_dist_ne_top with d_nat h_eq
          norm_cast at h_within_radius
          simp only [ENat.toNat_coe, ge_iff_le]
          omega
        omega
      · -- ⊢ `k ≤ domain_size`. This holds by the problem setup.
        simp only [k, domain_size]
        rw [sDomain_card 𝔽q β (h_i := by omega), hF₂.out]
        apply Nat.pow_le_pow_right (by omega) -- ⊢ ℓ - ↑i ≤ ℓ + 𝓡 - ↑⟨↑i, ⋯⟩
        simp only [tsub_le_iff_right]
        omega
      · -- ⊢ Function.Injective ωs
        simp only [ωs]
        -- The composition of two injective functions (`Equiv.symm` and `Subtype.val`) is injective.
        exact Function.Injective.comp Subtype.val_injective (Equiv.injective _)
      · -- ⊢ `p.natDegree < k`. This is true from `hp_deg`.
        exact natDeg_p_lt_k
      · -- ⊢ `Δ₀(f_vals, (fun a ↦ Polynomial.eval a p) ∘ ωs) ≤ e`
        change hammingDist f_vals ((fun a ↦ Polynomial.eval a p) ∘ ωs) ≤ e
        simp only [ωs]
        have h_functions_eq : (fun a ↦ Polynomial.eval a p) ∘ ωs
          = g_closest ∘ domain_to_fin.symm := by
          ext j; simp only [Function.comp_apply, Fin.eta, ωs]
          rw [←hp_eval]
        rw [h_functions_eq]
        -- ⊢ Δ₀(f_vals, g_closest ∘ ⇑domain_to_fin.symm) ≤ e
        simp only [Fin.eta, ge_iff_le, f_vals]
        -- ⊢ Δ₀(fun j ↦ f (domain_to_fin.symm j), g_closest ∘ ⇑domain_to_fin.symm) ≤ e
        calc
          _ ≤ hammingDist f g_closest := by
            apply hammingDist_le_of_outer_comp_injective f g_closest domain_to_fin.symm
              (hg := by exact Equiv.injective domain_to_fin.symm)
          _ ≤ e := by exact h_dist_f
    simp only [ne_eq, berlekamp_welch_result]
    simp only [h_decoder_succeeds, reduceCtorEq, not_false_eq_true]
  let p : L[X] := berlekamp_welch_result.get (Option.ne_none_iff_isSome.mp h_ne_none)
  exact fun x => p.eval x.val

omit [CharP L 2] [NeZero ℓ] in
/-- `Δ₀(f, g) ≤ pair_fiberwiseDistance(f, g) * 2 ^ steps` -/
lemma hammingDist_le_fiberwiseDistance_mul_two_pow_steps (i : Fin ℓ) (steps : ℕ)
    [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩):
    Δ₀(f, g) ≤ (pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      steps h_i_add_steps (f := f) (g := g)) * 2 ^ steps := by
  let d_fw := pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    steps h_i_add_steps (f := f) (g := g)
  have h_dist_le_fw_dist_times_fiber_size : (hammingDist f g) ≤ d_fw * 2 ^ steps := by
    -- This proves `dist f g ≤ (fiberwiseDisagreementSet ... f g).ncard * 2 ^ steps`
    -- and lifts to ℕ∞. We prove the `Nat` version `hammingDist f g ≤ ...`,
    -- which is equivalent.
    -- Let ΔH be the finset of actually bad x points where f and g disagree.
    set ΔH := Finset.filter (fun x => f x ≠ g x) Finset.univ
    have h_dist_eq_card : hammingDist f g = ΔH.card := by
      simp only [hammingDist, ne_eq, ΔH]
    rw [h_dist_eq_card]
    -- Y_bad is the set of quotient points y that THERE EXISTS a bad fiber point x
    set Y_bad := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g
    simp only at * -- simplify domain indices everywhere
    -- ⊢ #ΔH ≤ Y_bad.ncard * 2 ^ steps
    have hFinType_Y_bad : Fintype Y_bad := by exact Fintype.ofFinite ↑Y_bad
    -- Every point of disagreement `x` must belong to a fiber over some `y` in `Y_bad`,
    -- BY DEFINITION of `Y_bad`. Therefore, `ΔH` is a subset of the union of the fibers
    -- of `Y_bad`
    have h_ΔH_subset_bad_fiber_points : ΔH ⊆ Finset.biUnion Y_bad
        (t := fun y => ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)) ''
          (Finset.univ : Finset (Fin ((2:ℕ)^steps)))).toFinset) := by
      -- ⊢ If any x ∈ ΔH, then x ∈ Union(qMap_total_fiber(y), ∀ y ∈ Y_bad)
      intro x hx_in_ΔH; -- ⊢ x ∈ Union(qMap_total_fiber(y), ∀ y ∈ Y_bad)
      simp only [ΔH, Finset.mem_filter] at hx_in_ΔH
      -- Now we actually apply iterated qMap into x to get y_of_x,
      -- then x ∈ qMap_total_fiber(y_of_x) by definition
      let y_of_x := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x
      apply Finset.mem_biUnion.mpr; use y_of_x
      -- ⊢ y_of_x ∈ Y_bad.toFinset ∧ x ∈ qMap_total_fiber(y_of_x)
      have h_elemenet_Y_bad :  y_of_x ∈ Y_bad := by
        -- ⊢ y ∈ Y_bad
        simp only [fiberwiseDisagreementSet, iteratedQuotientMap, ne_eq, Subtype.exists, mem_filter,
          mem_univ, true_and, Y_bad]
        -- one bad fiber point of y_of_x is x itself
        let XX := x.val
        have h_XX_in_source : XX ∈ sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) := by
          exact Submodule.coe_mem x
        use XX
        use h_XX_in_source
        -- ⊢ Ŵ_steps⁽ⁱ⁾(XX) = y (iterated quotient map) ∧ ¬f ⟨XX, ⋯⟩ = g ⟨XX, ⋯⟩
        have h_forward_iterated_qmap : Polynomial.eval XX
            (intermediateNormVpoly 𝔽q β h_ℓ_add_R_rate ⟨↑i, by omega⟩
              ⟨steps, by simp only; omega⟩) = y_of_x := by
          simp only [iteratedQuotientMap, XX, y_of_x];
        have h_eval_diff : f ⟨XX, by omega⟩ ≠ g ⟨XX, by omega⟩ := by
          unfold XX
          simp only [Subtype.coe_eta, ne_eq, hx_in_ΔH, not_false_eq_true]
        simp only [h_forward_iterated_qmap, Subtype.coe_eta, h_eval_diff,
          not_false_eq_true, and_self]
      simp only [h_elemenet_Y_bad, true_and]

      set qMapFiber := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y_of_x)
      simp only [coe_univ, Set.image_univ, Set.toFinset_range, mem_image, mem_univ, true_and]
      use (pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (x := x))
      have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
        (x := x) (y := y_of_x).mp (by rfl)
      exact h_res
    -- ⊢ #ΔH ≤ Y_bad.ncard * 2 ^ steps
    -- The cardinality of a subset is at most the cardinality of the superset.
    apply (Finset.card_le_card h_ΔH_subset_bad_fiber_points).trans
    -- The cardinality of a disjoint union is the sum of cardinalities.
    rw [Finset.card_biUnion]
    · -- The size of the sum is the number of bad fibers (`Y_bad.ncard`) times
      -- the size of each fiber (`2 ^ steps`).
      simp only [Set.toFinset_card]
      have h_card_fiber_per_quotient_point := card_qMap_total_fiber 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps
      simp only [Set.image_univ, Fintype.card_ofFinset,
        Subtype.forall] at h_card_fiber_per_quotient_point
      have h_card_fiber_of_each_y : ∀ y ∈ Y_bad,
          Fintype.card ((qMap_total_fiber 𝔽q β (i := ⟨↑i, by omega⟩) (steps := steps)
            (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)) ''
            ↑(Finset.univ : Finset (Fin ((2:ℕ)^steps)))) = 2 ^ steps := by
        intro y hy_in_Y_bad
        have hy_card_fiber_of_y := h_card_fiber_per_quotient_point (a := y) (b := by
          exact Submodule.coe_mem y)
        simp only [coe_univ, Set.image_univ, Fintype.card_ofFinset, hy_card_fiber_of_y]
      rw [Finset.sum_congr rfl h_card_fiber_of_each_y]
      -- ⊢ ∑ x ∈ Y_bad.toFinset, 2 ^ steps ≤ Y_bad.encard.toNat * 2 ^ steps
      simp only [sum_const, smul_eq_mul, ofNat_pos, pow_pos, _root_.mul_le_mul_right, ge_iff_le]
      -- ⊢ Fintype.card ↑Y_bad ≤ Nat.card ↑Y_bad
      simp only [Y_bad, d_fw, pair_fiberwiseDistance, le_refl]
    · -- Prove that the fibers for distinct quotient points y₁, y₂ are disjoint.
      intro y₁ hy₁ y₂ hy₂ hy_ne
      have h_disjoint := qMap_total_fiber_disjoint (i := ⟨↑i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (y₁ := y₁) (y₂ := y₂) (hy_ne := hy_ne)
      simp only [Function.onFun, coe_univ]
      exact h_disjoint
  exact h_dist_le_fw_dist_times_fiber_size

omit [CharP L 2] [NeZero ℓ] in
/-- if `d⁽ⁱ⁾(f⁽ⁱ⁾, g⁽ⁱ⁾) < d_{ᵢ₊steps} / 2` (fiberwise distance),
then `d(f⁽ⁱ⁾, g⁽ⁱ⁾) < dᵢ/2` (regular code distance) -/
lemma pairUDRClose_of_pairFiberwiseClose (i : Fin ℓ) (steps : ℕ)
    [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_fw_dist_lt : pair_fiberwiseClose 𝔽q β i steps h_i_add_steps f g) :
    pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (f := f)
      (g := g) := by
  unfold pair_fiberwiseClose at h_fw_dist_lt
  norm_cast at h_fw_dist_lt
  unfold pair_UDRClose
  set d_fw := pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    steps h_i_add_steps (f := f) (g := g)
  set d_cur := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
  -- d_cur = 2 ^ (ℓ + 𝓡 - i) - 2 ^ (ℓ - i) + 1
  set d_next := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i.val + steps, by omega⟩)
  -- d_next = 2 ^ (ℓ + 𝓡 - (i + steps)) - 2 ^ (ℓ - (i + steps)) + 1

  have h_le : 2 * Δ₀(f, g) ≤ 2 * (d_fw * 2 ^ steps) := by
    apply Nat.mul_le_mul_left
    apply hammingDist_le_fiberwiseDistance_mul_two_pow_steps
  -- h_fw_dist_lt : 2 * d_fw < BBF_CodeDistance 𝔽q β ⟨↑i + steps, ⋯⟩
  have h_2_fw_dist_le : 2 * d_fw ≤ d_next - 1 := by omega

  have h_2_fw_dist_mul_2_pow_steps_le :
    2 * (d_fw * 2 ^ steps) ≤ (d_next * 2 ^ steps - 2 ^ steps):= by
    rw [←mul_assoc]
    conv_rhs =>
      rw (occs := [2]) [←one_mul (2 ^ steps)];
      rw [←Nat.sub_mul (n := d_next) (m := 1) (k := 2 ^ steps)];
    apply Nat.mul_le_mul_right
    exact h_2_fw_dist_le

  have h_2_fw_dist_mul_2_pow_steps_le : (d_next * 2 ^ steps - 2 ^ steps) = d_cur - 1 := by
    dsimp only [d_next, d_cur]
    rw [BBF_CodeDistance_eq, BBF_CodeDistance_eq]
    simp only [add_tsub_cancel_right]
    rw [Nat.add_mul, Nat.sub_mul]
    rw [←Nat.pow_add, ←Nat.pow_add]
    have h_exp1 : ℓ + 𝓡 - (i.val + steps) + steps = ℓ + 𝓡 - i.val := by omega
    have h_exp2 : ℓ - (i.val + steps) + steps = ℓ - i.val := by omega
    rw [h_exp1, h_exp2]
    omega

  have h_le_2 : 2 * (d_fw * 2 ^ steps) ≤ BBF_CodeDistance 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) - 1:= by
    omega

  apply Nat.lt_of_le_pred (h := by simp only [d_cur, BBF_CodeDistance_eq]; omega)
  simp only [pred_eq_sub_one]
  exact Nat.le_trans h_le h_le_2


omit [CharP L 2] [DecidableEq 𝔽q] hF₂ [NeZero ℓ] [NeZero 𝓡] in
lemma exists_fiberwiseClosestCodeword (i : Fin ℓ) (steps : ℕ) [NeZero steps]
  (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    let S_i := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
    let C_i : Set (S_i → L) := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
    ∃ (g : S_i → L), g ∈ C_i ∧
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) steps (h_i_add_steps := h_i_add_steps) (f := f) =
        pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps (h_i_add_steps := h_i_add_steps) (f := f) (g := g) := by
  simp only [SetLike.mem_coe]
  set S_i := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
  set C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  -- Let `S` be the set of all possible fiber-wise disagreement sizes.
  let S := (fun (g : C_i) =>
    (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).card) '' Set.univ
  -- The code `C_i` (a submodule) is non-empty, so `S` is also non-empty.
  have hS_nonempty : S.Nonempty := by
    refine Set.image_nonempty.mpr ?_

    exact Set.univ_nonempty
  -- For a non-empty set of natural numbers, `sInf` is an element of the set.
  have h_sInf_mem : sInf S ∈ S := Nat.sInf_mem hS_nonempty
  -- By definition, `d_fw = sInf S`.
  -- Since `sInf S` is in the image set `S`, there must be an element `g_subtype` in the domain
  -- (`C_i`) that maps to it. This `g_subtype` is the codeword we're looking for.
  rw [Set.mem_image] at h_sInf_mem
  rcases h_sInf_mem with ⟨g_subtype, _, h_eq⟩
  -- Extract the codeword and its membership proof.
  refine ⟨g_subtype, ?_, ?_⟩
  · -- membership
    exact g_subtype.property
  · -- equality of distances
    -- `fiberwiseDistance` is defined as the infimum of `S`, so it equals `sInf S`
    -- and `h_eq` tells us that this is exactly the distance to `g_subtype`.
    -- You may need to unfold `fiberwiseDistance` here if Lean doesn't reduce it automatically.
    exact id (Eq.symm h_eq)

omit [CharP L 2] [NeZero ℓ] in
/-- if `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) < d_{ᵢ₊steps} / 2` (fiberwise distance),
then `d(f⁽ⁱ⁾, C⁽ⁱ⁾) < dᵢ/2` (regular code distance) -/
theorem UDRClose_of_fiberwiseClose (i : Fin ℓ) (steps : ℕ)
    [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  (h_fw_dist_lt : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) (h_i_add_steps := h_i_add_steps) (f := f)) :
  UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ f := by
  unfold fiberwiseClose at h_fw_dist_lt
  unfold UDRClose
  -- 2 * Δ₀(f, ↑(BBF_Code 𝔽q β ⟨↑i, ⋯⟩)) < ↑(BBF_CodeDistance ℓ 𝓡 ⟨↑i, ⋯⟩)
  set d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f
  let C_i := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  let d_H := Δ₀(f, C_i)
  let d_i := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
  let d_i_plus_steps := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i.val + steps, by omega⟩)

  have h_d_i_gt_0 : d_i > 0 := by
    dsimp [d_i, BBF_CodeDistance] -- ⊢ 2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) + 1 > 0
    have h_exp_lt : ℓ - i.val < ℓ + 𝓡 - i.val := by
      exact Nat.sub_lt_sub_right (a := ℓ) (b := ℓ + 𝓡) (c := i.val) (by omega) (by
        apply Nat.lt_add_of_pos_right; exact pos_of_neZero 𝓡)
    have h_pow_lt : 2 ^ (ℓ - i.val) < 2 ^ (ℓ + 𝓡 - i.val) := by
      exact Nat.pow_lt_pow_right (by norm_num) h_exp_lt
    simp_rw [BBF_CodeDistance_eq]
    omega

  have h_C_i_nonempty : Nonempty C_i := by
    simp only [nonempty_subtype, C_i]
    exact Submodule.nonempty (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i.val, by omega⟩)

  -- 1. Relate Hamming distance `d_H` to fiber-wise distance `d_fw`.
  obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw
    = (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g').card := by
    apply exists_fiberwiseClosestCodeword

  have h_UDR_close_f_g' := pairUDRClose_of_pairFiberwiseClose 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    (h_i_add_steps := h_i_add_steps) (f := f) (g := g') (h_fw_dist_lt := by
      dsimp only [pair_fiberwiseClose, pair_fiberwiseDistance]; norm_cast;
      rw [←h_g'_min_card];
      exact (by norm_cast at h_fw_dist_lt)
    )
  -- ⊢ 2 * Δ₀(f, ↑(BBF_Code 𝔽q β ⟨↑i, ⋯⟩)) < ↑(BBF_CodeDistance 𝔽q β ⟨↑i, ⋯⟩)
  calc
    2 * Δ₀(f, C_i) ≤ 2 * Δ₀(f, g') := by
      rw [ENat.mul_le_mul_left_iff (ha := by
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])
        (h_top := by simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true])
      ]
      apply Code.distFromCode_le_dist_to_mem (C := C_i) (u := f) (v := g') (hv := h_g'_mem)
    _ < _ := by norm_cast -- use result from h_UDR_close_f_g'

omit [CharP L 2] [NeZero ℓ] in
/-- This expands `exists_fiberwiseClosestCodeword` to the case `f` is fiberwise-close to `C_i`. -/
lemma exists_unique_fiberwiseClosestCodeword_within_UDR (i : Fin ℓ)
    (steps : ℕ) [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_fw_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) (h_i_add_steps := h_i_add_steps) (f := f)) :
    let S_i := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
    let C_i : Set (S_i → L) := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
    ∃! (g : S_i → L), (g ∈ C_i) ∧
      (fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) steps (h_i_add_steps := h_i_add_steps) (f := f) =
        pair_fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps (h_i_add_steps := h_i_add_steps) (f := f) (g := g)) ∧
      (g = UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ f
        (h_within_radius := UDRClose_of_fiberwiseClose 𝔽q β i steps h_i_add_steps f h_fw_close))
      := by
  set d_fw := fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    steps h_i_add_steps f
  set S_i := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
  set S_i_next := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
  set C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  obtain ⟨g, h_g_mem, h_g_min_card⟩ : ∃ g ∈ C_i, d_fw
    = (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).card := by
    apply exists_fiberwiseClosestCodeword
  set C_i_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩
  have h_neZero_dist_C_i_next : NeZero (‖(C_i_next : Set (S_i_next → L))‖₀) := {
    out := by
      unfold C_i_next
      simp_rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩)]
      omega
  }
  have h_neZero_dist_C_i : NeZero (‖(C_i : Set (S_i → L))‖₀) := {
    out := by
      unfold C_i
      simp_rw [BBF_CodeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)]
      omega
  }
  use g
  have h_f_g_UDR_close : Δ₀(f, g) ≤ Code.uniqueDecodingRadius (F := L)
    (ι := S_i) (C := C_i) := by -- This relies on `h_fw_close`
    unfold fiberwiseClose at h_fw_close
    norm_cast at h_fw_close
    rw [←Code.UDRClose_iff_two_mul_proximity_lt_d_UDR] at h_fw_close
    unfold d_fw at h_g_min_card
    rw [h_g_min_card] at h_fw_close
    rw [Code.uniqueDecodingRadius, ←Nat.two_mul_lt_iff_le_half_of_sub_one (a := #(fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g)) (h_b_pos := by exact Nat.pos_of_neZero (n := ‖(C_i_next : Set (S_i_next → L))‖₀))] at h_fw_close
    -- h_fw_close : 2 * #(fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g) < ‖↑(BBF_Code 𝔽q β ⟨↑i + steps, ⋯⟩)‖₀
    rw [Code.uniqueDecodingRadius, ←Nat.two_mul_lt_iff_le_half_of_sub_one (a := Δ₀(f,g)) (h_b_pos := by exact Nat.pos_of_neZero (n := ‖(C_i : Set (S_i → L))‖₀))]
    -- 2 * Δ₀(f, g) < ‖↑(C_i)‖₀
    let res := pairUDRClose_of_pairFiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps (h_i_add_steps := h_i_add_steps) (f := f) (g := g) (h_fw_dist_lt := by
      unfold pair_fiberwiseClose pair_fiberwiseDistance
      norm_cast
    )
    exact res

  let h_f_UDR_close := UDRClose_of_fiberwiseClose 𝔽q β i steps h_i_add_steps f h_fw_close
  have h_g_eq_UDRCodeword : g = UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨i, by omega⟩ f h_f_UDR_close := by
    apply Code.eq_of_le_uniqueDecodingRadius (C := C_i) (u := f)
      (v := g) (w := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ f h_f_UDR_close) (hv := h_g_mem) (hw := by apply UDRCodeword_mem_BBF_Code (i := ⟨i, by omega⟩) (f := f) (h_within_radius := h_f_UDR_close))
      (huv := by
        -- ⊢ Δ₀(f, g) ≤ uniqueDecodingRadius ↑C_i
        exact h_f_g_UDR_close
      )
      (huw := by
        apply dist_to_UDRCodeword_le_uniqueDecodingRadius (i := ⟨i, by omega⟩) (f := f) (h_within_radius := h_f_UDR_close)
      )
  simp only
  constructor
  · constructor
    · exact h_g_mem
    · constructor
      · exact h_g_min_card
      · -- ⊢ g = UDRCodeword 𝔽q β ⟨↑i, ⋯⟩ f ⋯
        exact h_g_eq_UDRCodeword
  · -- trivial contrapositive case
    intro y hy_mem_C_i
    rw [h_g_eq_UDRCodeword]
    rw [hy_mem_C_i.2.2]

omit [CharP L 2] [NeZero ℓ] in
/-- **Lemma: Single Step BBF_Code membership preservation**
It establishes that folding a codeword from the i-th code produces a codeword in the (i+1)-th code.
This relies on **Lemma 4.13** that 1-step folding advances the evaluation polynomial. -/
lemma fold_preserves_BBF_Code_membership (i : Fin ℓ) (h_i_succ_lt : i + 1 < ℓ + 𝓡)
    (f : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩))
    (r_chal : L) :
    (fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ (by omega) f r_chal) ∈
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + 1, by omega⟩) := by
  -- 1. Unwrap the code definition to get the polynomial P
  -- BBF_Code is ReedSolomon, so f comes from some P with deg < 2^(ℓ-i)
  set C_cur := ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    : Set ((sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L)) with h_C_cur
  have h_f_mem : f.val ∈ C_cur := by
    unfold C_cur
    simp only [Subtype.coe_prop]
  simp only [BBF_Code, code, C_cur] at h_f_mem
  rcases h_f_mem with ⟨P, hP_deg, hP_eval⟩ -- the poly that generates `f` on `S^(i)`
  let iNovel_coeffs : Fin (2^(ℓ - i)) → L :=
    getINovelCoeffs 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (P := P)
  simp only [evalOnPoints, Embedding.coeFn_mk, LinearMap.coe_mk, AddHom.coe_mk] at hP_eval
  simp only [SetLike.mem_coe, mem_degreeLT, cast_pow, cast_ofNat] at hP_deg
  -- ⊢ Fin (2 ^ (ℓ - ↑i)) → L
  simp only [BBF_Code, code, Submodule.mem_map]
  set new_coeffs := fun j : Fin (2^(ℓ - (i + 1))) =>
  (1 - r_chal) * (iNovel_coeffs ⟨j.val * 2, by
    rw [←Nat.add_zero (j.val * 2)]
    apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
      (i := 0) (by omega) (by omega)
  ⟩) +
  r_chal * (iNovel_coeffs ⟨j.val * 2 + 1, by
    apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
      (i := 1) (by omega) (by omega)
  ⟩)
  set P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := ⟨i+1, by omega⟩) new_coeffs
  use P_i_plus_1
  constructor
  · -- ⊢ P_i_plus_1 ∈ L[X]_(2 ^ (ℓ - (↑i + 1)))
    apply Polynomial.mem_degreeLT.mpr
    unfold P_i_plus_1
    apply degree_intermediateEvaluationPoly_lt
  · -- ⊢ (evalOnPoints ... P_i_plus_1) = fold 𝔽q β ⟨↑i, ⋯⟩ h_i_succ_lt (↑f) r_chal
    let fold_advances_evaluation_poly_res := fold_advances_evaluation_poly 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i_succ_lt := h_i_succ_lt)
      (coeffs := iNovel_coeffs) (r_chal := r_chal)
    simp only at fold_advances_evaluation_poly_res
    funext (y : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i+1, by omega⟩)
    dsimp only [evalOnPoints, Embedding.coeFn_mk, LinearMap.coe_mk, AddHom.coe_mk]
    -- ⊢ Polynomial.eval (↑y) P_i_plus_1 = fold 𝔽q β ⟨↑i, ⋯⟩ h_i_succ_lt (↑f) r_chal y
    unfold polyToOracleFunc at fold_advances_evaluation_poly_res
    let lhs_eq := congrFun fold_advances_evaluation_poly_res y
    conv_lhs => rw [←lhs_eq]
    simp only [Subtype.coe_eta]
    congr 1
    funext (x : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩)
    -- ⊢ Polynomial.eval (↑x) (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
      -- ⟨↑i, ⋯⟩ iNovel_coeffs) = ↑f x
    unfold intermediateEvaluationPoly iNovel_coeffs
    simp only [Fin.eta]
    let res := intermediateEvaluationPoly_from_inovel_coeffs_eq_self 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (P := P) (hP_deg := hP_deg)
    unfold intermediateEvaluationPoly at res
    rw [res]
    -- ⊢ Polynomial.eval (↑x) P = ↑f x
    exact (congrFun hP_eval x)

omit [CharP L 2] [NeZero ℓ] in
/-- **Lemma: Iterated BBF_Code membership preservation (Induction)**
If `f` is in BBF_Code `C^{(i)}`, then `iterated_fold f r` is in BBF_Code `C^{(i+steps)}`.
NOTE: we can potentially specifify the structure of the folded polynomial. -/
lemma iterated_fold_preserves_BBF_Code_membership (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i + steps ≤ ℓ)
    (f : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩))
    (r_challenges : Fin steps → L) :
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps) (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (f := f) (r_challenges := r_challenges)) ∈
    (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩) := by
  induction steps generalizing i with
  | zero =>
    -- Base case: 0 steps. iterated_fold is identity. Code is the same.
    simp only [Nat.add_zero, iterated_fold, reduceAdd, Fin.val_succ, id_eq, Fin.dfoldl_zero,
      SetLike.coe_mem]
  | succ k ih =>
    -- 1. Perform k steps first
    let f_k := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (steps := k) (h_i_add_steps := by simp only; omega) (f := f)
      (r_challenges := Fin.init r_challenges)
    -- 2. Apply IH: f_k is in C^{(i+k)}
    have h_fk_mem : f_k ∈ BBF_Code 𝔽q β ⟨i + k, by omega⟩ := by
      apply ih (i := i) (h_i_add_steps := by omega)
    set f_k_code_word : (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + k, by omega⟩) :=
      ⟨f_k, h_fk_mem⟩
    -- 3. Perform the (k+1)-th fold on f_k
    rw [iterated_fold_last] -- (Helper lemma needed to unroll recursion)
    -- 4. Apply the Single Step Lemma
    let res := fold_preserves_BBF_Code_membership (i := ⟨i + k, by omega⟩)
      (h_i_succ_lt := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
      (f := f_k_code_word) (r_chal := r_challenges (Fin.last k))
    exact res

/--
Compliance condition (Definition 4.17) : For an index `i` that is a multiple of `steps`,
the oracle `f_i` is compliant if it's close to the code fiber-wise, the next oracle
`f_i_plus_steps` is close to its code, and their unique closest codewords are consistent
with folding.
-/
def isCompliant (i : Fin (ℓ)) (steps : ℕ) [NeZero steps]
  (h_i_add_steps : i + steps ≤ ℓ)
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  (f_i_plus_steps : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i + steps, by omega⟩)
  (challenges : Fin steps → L) : Prop :=
  ∃ (h_fw_dist_lt : 2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps) h_i_add_steps f_i < (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩) : ℕ∞))
    (h_dist_next_lt : 2 * Δ₀(f_i_plus_steps, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩))
      < (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩) : ℕ∞)), -- note that two lts are equal
    -- Third constraint : the DECODED codewords are consistent via the iterated_fold
    let h_dist_curr_lt := UDRClose_of_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps h_i_add_steps f_i
      (h_fw_dist_lt := h_fw_dist_lt)
    let f_bar_i := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i, by omega⟩) f_i h_dist_curr_lt
    let f_bar_i_plus_steps := UDRCodeword 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩)
      f_i_plus_steps h_dist_next_lt
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps) (i := ⟨i, by omega⟩)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
      f_bar_i challenges = f_bar_i_plus_steps

omit [CharP L 2] [NeZero ℓ] in
/--
Farness implies non-compliance. If `f_i` is far from its code `C_i`, it cannot be
compliant. This follows directly from the contrapositive of
`fiberwise_dist_lt_imp_dist_lt`.
-/
lemma farness_implies_non_compliance (i : Fin ℓ) (steps : ℕ) [NeZero steps]
  (h_i_add_steps : i + steps ≤ ℓ)
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  (f_i_plus_steps : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    ⟨i + steps, by omega⟩)
  (challenges : Fin steps → L)
  (h_far : 2 * Δ₀(f_i, (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩))
    ≥ (BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) : ℕ∞)) :
  ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    h_i_add_steps f_i f_i_plus_steps challenges :=
by -- We use our key theorem that "fiber-wise close" implies "Hamming close".
  intro h_compliant
  rcases h_compliant with ⟨h_fw_dist_lt, _, _⟩
  have h_close := UDRClose_of_fiberwiseClose 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) h_i_add_steps f_i
    h_fw_dist_lt
  have h_not_far := LT.lt.not_ge h_close
  exact h_not_far h_far

/-- **Fold error containment**: Two words achieve `fold error containment` for a specific tuple of challenges if folding them does not
introduce new errors outside of their fiberwise disagreement set. -/
def fold_error_containment (i : Fin ℓ) (steps : ℕ)  (h_i_add_steps : i + steps ≤ ℓ)
    (f f_bar : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ → L)
    (r_challenges : Fin steps → L) :=
    let fiberwise_Δ_set := fiberwiseDisagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by omega) (f := f) (g := f_bar)
    let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps) (i := ⟨i, by omega⟩)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (f := f) (r_challenges := r_challenges)
    let folded_f_bar := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps) (i := ⟨i, by omega⟩)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (f := f_bar) (r_challenges := r_challenges)
    let folded_Δ_set := disagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩) (f := folded_f) (g := folded_f_bar)
    folded_Δ_set ⊆ fiberwise_Δ_set

/-! **Lemma 4.18.** For each `i ∈ {0, steps, ..., ℓ-steps}`, if `f⁽ⁱ⁾` is `UDR-close`, then, for each tuple of folding challenges `(rᵢ', ..., r_{i+steps-1}') ∈ L^steps`, we have that `fold error containment` holds.
-- * **Main Idea of Proof:** Proceeds by contraposition. If `y ∉ Δ⁽ⁱ⁾(f⁽ⁱ⁾, f̄⁽ⁱ⁾)`, then the restrictions of `f⁽ⁱ⁾` and `f̄⁽ⁱ⁾` to the fiber over `y` are identical. By Definition 4.8, this implies their folded values at `y` are also identical.
-- * **Intuition**: Because folding is local (Def 4.8), if `f⁽ⁱ⁾` and `f̄⁽ⁱ⁾` agree completely on the fiber above a point `y`, their folded values at `y` must also agree.
-- * **Consequence**: If `f⁽ⁱ⁾` is close to `f̄⁽ⁱ⁾`, then `fold(f⁽ⁱ⁾)` must be close to `fold(f̄⁽ⁱ⁾)`.
-/
lemma fold_error_containment_of_UDRClose (i : Fin ℓ) (steps : ℕ) [NeZero steps]
  (h_i_add_steps : i + steps ≤ ℓ)
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  (challenges : Fin steps → L)
  (h_UDRClose : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) f_i) :
  let f_bar := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) f_i h_UDRClose
  fold_error_containment 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) h_i_add_steps f_i f_bar challenges := by
-- 1. Unfold definitions
  unfold fold_error_containment disagreementSet fiberwiseDisagreementSet

  set f_bar := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) f_i h_UDRClose

  -- 2. Start the subset proof
  simp only
  intro y -- convert subset relation to membership implication of y
  -- ⊢ **y in folded disagreement set → y in fiberwise disagreement set**
  intro hy_in_folded_disagreement -- ⊢ **y in fiberwise disagreement set**

  -- 3. Proof by contradiction (or contraposition logic)
  -- The hypothesis says: folded_f(y) ≠ folded_f_bar(y)
  simp only [ne_eq, mem_filter, mem_univ, true_and] at hy_in_folded_disagreement

  -- We want to show y ∈ fiberwiseDisagreementSet
  -- This means: ∃ x in fiber(y), f(x) ≠ f_bar(x)
  -- Let's assume the opposite: ∀ x in fiber(y), f(x) = f_bar(x)
  by_contra h_not_in_fiber_disagreement
  simp only [Fin.eta, ne_eq, Subtype.exists, mem_filter, mem_univ, true_and, not_exists, not_and,
    Decidable.not_not] at h_not_in_fiber_disagreement

  -- 4. Use Lemma 4.9 (iterated_fold_eq_matrix_form) to express the fold operation
  -- We need to show that if the fiber inputs are equal, the folded output is equal.

  let folded_f_y := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps)
      (i := ⟨i, by omega⟩) (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
      (f := f_i) (r_challenges := challenges) (y := y)

  let folded_f_bar_y := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps)
      (i := ⟨i, by omega⟩) (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
      (f := f_bar) (r_challenges := challenges) (y := y)

  -- Apply the matrix form lemma to both sides
  have h_matrix_f := iterated_fold_eq_matrix_form 𝔽q β (i := i) (steps := steps) (h_i_add_steps := by omega) (f := f_i) (r_challenges := challenges)
  have h_matrix_f_bar := iterated_fold_eq_matrix_form 𝔽q β (i := i) (steps := steps) (h_i_add_steps := by omega) (f := f_bar) (r_challenges := challenges)

  rw [h_matrix_f] at hy_in_folded_disagreement
  rw [h_matrix_f_bar] at hy_in_folded_disagreement

  -- 5. Show the RHS of the matrix forms are equal
  -- The RHS depends on `localized_fold_matrix_form`.
  -- This function depends on `foldMatrix` (same for both) and `fiberEvaluations`.
  -- We just need to show `fiberEvaluations` is the same for both.

  set fiberEvals_f_i := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (f := f_i) y
  set fiberEvals_f_bar_i := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (f := f_bar) y
  have h_fiber_evals_eq : fiberEvals_f_i = fiberEvals_f_bar_i := by
    ext k
    unfold fiberEvals_f_i fiberEvals_f_bar_i fiberEvaluations
    -- The k-th fiber point x is:
    let x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_i_add_steps := by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) y k

    -- We need to show f_i(x) = f_bar(x).
    -- This follows from our contradiction hypothesis `h_not_in_fiber_disagreement`.
    apply h_not_in_fiber_disagreement x

    -- We must prove x is actually in the fiber of y (which is true by construction/definition)
    -- Use the lemma `generates_quotient_point_if_is_fiber_of_y` or similar
    let res := generates_quotient_point_if_is_fiber_of_y 𝔽q β (i := i) (steps := steps) (h_i_add_steps := by omega) (x := x) (y := y) (hx_is_fiber := by use k)
    exact res.symm

  -- 6. Final Contradiction
  -- Since the fiber evaluations are equal, the matrix products must be equal.
  -- localized_fold_matrix_form is just a function of these evaluations.
  have h_folded_eq : localized_fold_matrix_form 𝔽q β (i := i) (steps := steps) (h_i_add_steps := by omega) (f := f_i) (r_challenges := challenges) y =
                     localized_fold_matrix_form 𝔽q β (i := i) (steps := steps) (h_i_add_steps := by omega) (f := f_bar) (r_challenges := challenges) y := by
    unfold localized_fold_matrix_form
    simp only
    unfold fiberEvals_f_i fiberEvals_f_bar_i at h_fiber_evals_eq
    rw [h_fiber_evals_eq]

  -- Contradiction: We proved they are equal, but hypothesis says they are unequal.
  exact hy_in_folded_disagreement h_folded_eq

open Classical in
/-- **Definition 4.19** Bad event for folding : This event captures two scenarios where the
random folding challenges undermine the protocol's soundness checks.
For `i ∈ {0, ..., ℓ - steps}`,
- In case `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) < dᵢ₊steps / 2` (fiberwise close):
  `Δ⁽ⁱ⁾(f⁽ⁱ⁾, f̄⁽ⁱ⁾) ⊄ Δ(fold(f⁽ⁱ⁾, rᵢ', ..., r_{i+steps-1}'), fold(f̄⁽ⁱ⁾, rᵢ', ..., r_{i+steps-1}'))`, i.e. fiberwiseDisagreementSet ⊄ foldedDisagreementSet
- In case `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) ≥ dᵢ₊steps / 2`  (fiberwise far):
  `d(fold(f⁽ⁱ⁾, rᵢ', ..., rᵢ₊steps₋₁'), C⁽ⁱ⁺steps⁾) < dᵢ₊steps / 2`, i.e. foldedUDRClose -/
def foldingBadEvent (i : Fin ℓ) (steps : ℕ) [NeZero steps] (h_i_add_steps : i + steps ≤ ℓ)
  (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  (r_challenges : Fin steps → L) : Prop :=

  let folded_f_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
    (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (f := f_i) (r_challenges := r_challenges)

  if h_is_close : (fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) (h_i_add_steps := h_i_add_steps) (f := f_i)) then
    -- Case 1 : The oracle `f_i` is fiber-wise "close" to the code.
    -- The bad event is when folding causes disagreements to vanish, violating Lemma 4.18.
    -- This happens if the random challenges are unlucky.

    let f_bar_i := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩ (f := f_i) (h_within_radius := UDRClose_of_fiberwiseClose 𝔽q β i steps h_i_add_steps f_i h_is_close)

    let folded_f_bar_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
       (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (f := f_bar_i) (r_challenges := r_challenges)

    -- The Bad Condition: FiberDisagreements ⊈ FoldedDisagreements
    ¬ (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps (f := f_i) (g := f_bar_i) ⊆
       disagreementSet 𝔽q β ⟨i+steps, by omega⟩ folded_f_i folded_f_bar_i)

  else
    -- Case 2 : The oracle `f_i` is fiber-wise "far" from the code.
    -- Folding a "far" function should result in another "far" function.
    -- The bad event is when folding makes this far function appear "close" to the code.
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩ folded_f_i

end SoundnessTools
end
end Binius.BinaryBasefold
