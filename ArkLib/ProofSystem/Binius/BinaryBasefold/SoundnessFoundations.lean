import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

namespace Binius.BinaryBasefold

/-! **Soundness foundational Lemmas (Lemmas 4.20 - 4.25)**
- Probability reasoning: using lemmas in `DG25.lean`
- Foundational definitions and lemmas: `ArkLib.Data.FieldTheory.AdditiveNTT.AdditiveNTT.lean`
  and `ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude`
- Raw proof specs: `ArkLib/ProofSystem/Binius/BinaryBasefold/SoundnessFoundationsSpec.md`
-/

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

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

/-- Helper to convert an index `k` into a vector of bits (a1s field elements). -/
def bitsOfIndex {n : ℕ} (k : Fin (2 ^ n)) : Fin n → L :=
  fun i => if Nat.testBit k i then 1 else 0

omit [Fintype L] [DecidableEq L] [CharP L 2] in
lemma multilinearWeight_bitsOfIndex_eq_indicator {n : ℕ} (j k : Fin (2 ^ n)) :
  multilinearWeight (F := L) (r := bitsOfIndex k) (i := j) = if j = k then 1 else 0 := by
  set r_k := bitsOfIndex (L := L) k with h_r_k
  unfold multilinearWeight
  -- NOTE: maybe we can generalize this into a lemma?
  -- ⊢ (∏ j_1, if (↑j).testBit ↑j_1 = true then r_k j_1 else 1 - r_k j_1) = if j = k then 1 else 0
  dsimp only [bitsOfIndex, r_k]
  simp_rw [Nat.testBit_eq_getBit]
  by_cases h_eq : j = k
  · simp only [h_eq, ↓reduceIte]
    have h_eq: ∀ (x : Fin n),
      ((if (x.val).getBit ↑k = 1 then if (x.val).getBit ↑k = 1 then (1 : L) else (0 : L) else 1 - if (x.val).getBit ↑k = 1 then (1 : L) else (0 : L))) = (1 : L) := by
        intro x
        by_cases h_eq : (x.val).getBit ↑k = 1
        · simp only [h_eq, ↓reduceIte]
        · simp only [h_eq, ↓reduceIte, sub_zero]
    simp_rw [h_eq]
    simp only [prod_const_one]
  · simp only [h_eq, ↓reduceIte]
    -- ⊢ (∏ x, if (↑x).getBit ↑j = 1 then if (↑x).getBit ↑k = 1 then 1 else 0 else 1 - if (↑x).getBit ↑k = 1 then 1 else 0) = 0
    rw [Finset.prod_eq_zero_iff]
    --         ⊢ ∃ a ∈ univ,
    -- (if (↑a).getBit ↑j = 1 then if (↑a).getBit ↑k = 1 then 1 else 0 else 1 - if (↑a).getBit ↑k = 1 then 1 else 0) = 0
    let exists_bit_diff_idx := Nat.exist_bit_diff_if_diff (a := j) (b := k) (h_a_ne_b := h_eq)
    rcases exists_bit_diff_idx with ⟨bit_diff_idx, h_bit_diff_idx⟩
    have h_getBit_of_j_lt_2 : Nat.getBit (k := bit_diff_idx.val) (n := j) < 2 := by
      exact Nat.getBit_lt_2 (k := bit_diff_idx.val) (n := j)
    have h_getBit_of_k_lt_2 : Nat.getBit (k := bit_diff_idx.val) (n := k) < 2 := by
      exact Nat.getBit_lt_2 (k := bit_diff_idx.val) (n := k)
    use bit_diff_idx
    constructor
    · simp only [mem_univ]
    · by_cases h_bit_diff_of_j_eq_0 : Nat.getBit (k := bit_diff_idx.val) (n := j) = 0
      · simp only [h_bit_diff_of_j_eq_0, zero_ne_one, ↓reduceIte]
        -- ⊢ (1 - if (↑bit_diff_idx).getBit ↑k = 1 then 1 else 0) = 0
        have h_bit_diff_of_k_eq_1 : Nat.getBit (k := bit_diff_idx.val) (n := k) = 1 := by
          omega
        simp only [h_bit_diff_of_k_eq_1, ↓reduceIte, sub_self]
      · have h_bit_diff_of_j_eq_1 :
          Nat.getBit (k := bit_diff_idx.val) (n := j) = 1 := by
          omega
        have h_bit_diff_of_k_eq_0 : Nat.getBit (k := bit_diff_idx.val) (n := k) = 0 := by
          omega
        simp only [h_bit_diff_of_j_eq_1, ↓reduceIte, h_bit_diff_of_k_eq_0, zero_ne_one]

omit [Fintype L] [DecidableEq L] [CharP L 2] in
/-- **Key Property of Tensor Expansion with Binary Challenges**:
When `r = bitsOfIndex k`, the tensor expansion `challengeTensorExpansion n r`
is the indicator vector for index `k` (i.e., 1 at position `k`, 0 elsewhere).
This is a fundamental property used in both Proposition 4.20 and Lemma 4.21. -/
lemma challengeTensorExpansion_bitsOfIndex_is_eq_indicator {n : ℕ} (k : Fin (2 ^ n)) :
    -- Key Property: Tensor(r_k) is the indicator vector for k.
    -- Tensor(r_k)[j] = 1 if j=k, 0 if j≠k.
    challengeTensorExpansion n (r := bitsOfIndex (L := L) k) = fun j => if j = k then 1 else 0 := by
  -- Let r_k be the bit-vector corresponding to index k
  funext j
  unfold challengeTensorExpansion
  -- ⊢ multilinearWeight r_k j = if j = k then 1 else 0
  apply multilinearWeight_bitsOfIndex_eq_indicator

noncomputable section

section Lift_PreTensorCombine

/-! **Interleaved Word Construction (Supporting definition for Lemma 4.21)**
Constructs the rows `f_j^{(i+steps)}` of the interleaved word.
For a fixed row index `j` and a domain point `y ∈ S^{i+steps}`,
the value is the `j`-th entry of the vector `M_y * fiber_vals`.
-- NOTE: the way we define `ι` as `sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩` instead of
`Fin` requires using the generic versions of code/proximity gap lemmas.
We don't have a unified mat-mul formula for this, because the `M_y` matrix varies over `y` -/
def preTensorCombine_WordStack (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    WordStack (A := L) (κ := Fin (2 ^ steps))
      (ι := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩) := fun j y =>
    -- 1. Calculate the folding matrix M_y
    let M_y : Matrix (Fin (2 ^ steps)) (Fin (2 ^ steps)) L :=
      foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      h_destIdx h_destIdx_le (y := y)
    -- 2. Get the evaluation of f on the fiber of y
    let fiber_vals : Fin (2 ^ steps) → L :=
      fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      h_destIdx h_destIdx_le (f := f_i) y
    -- 3. The result is the j-th component of the matrix-vector product
    (M_y *ᵥ fiber_vals) j

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **Folding with Binary Challenges selects a Matrix Row**
This lemma establishes the geometric link:
The `j`-th row of the `preTensorCombine` matrix product is exactly equal to
folding the function `f` using the bits of `j` as challenges.
This holds for ANY function `f`, not just codewords.
-/
lemma preTensorCombine_row_eq_fold_with_binary_row_challenges
    (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (rowIdx : Fin (2 ^ steps)) :
    ∀ y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩,
      (preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps f) rowIdx y =
      iterated_fold 𝔽q β ⟨i, by omega⟩ steps
        (by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (f := f)
          (r_challenges := bitsOfIndex (L := L) (n := steps) rowIdx) (y := y) := by
  simp only [Subtype.forall]
  set S_next := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩ with h_S_next
  intro y hy_mem_S_next
  -- 1. Expand the definition of preTensorCombine (The LHS)
  -- LHS = (M_y * f_vals)[rowIdx]
  dsimp [preTensorCombine_WordStack]
  -- 2. Expand the matrix form of iterated_fold (The RHS)
  -- RHS = Tensor(r) • (M_y * f_vals)
  rw [iterated_fold_eq_matrix_form 𝔽q β h_destIdx h_destIdx_le]
  unfold localized_fold_matrix_form single_point_localized_fold_matrix_form
  -- 3. Use the Tensor Property
  -- Tensor(bits(rowIdx)) is the indicator vector for rowIdx
  let tensor := challengeTensorExpansion (L := L) steps (bitsOfIndex rowIdx)
  have h_indicator : tensor = fun k => if k = rowIdx then 1 else 0 :=
    challengeTensorExpansion_bitsOfIndex_is_eq_indicator (L := L) rowIdx
  simp only
  -- 4. Simplify the Dot Product
  -- (Indicator • Vector) is exactly Vector[rowIdx]
  dsimp only [tensor] at h_indicator
  rw [h_indicator]
  rw [dotProduct]
  simp only [boole_mul]
  rw [Finset.sum_eq_single rowIdx]
  · -- The term at rowIdx is (1 * val)
    simp only [if_true]
  · -- All other terms are 0
    intro b _ hb_ne
    simp [hb_ne]
  · -- rowIdx is in the domain
    intro h_notin
    exact (h_notin (Finset.mem_univ rowIdx)).elim

omit [CharP L 2] [NeZero ℓ] in
lemma preTensorCombine_is_interleavedCodeword_of_codeword (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i + steps ≤ ℓ)
    (f : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    (⋈|(preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps f)) ∈
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩ ^⋈ (Fin (2 ^ steps))) := by
  -- 1. Interleaved Code Definition: "A word is in the interleaved code iff every row is in the base code"
  set S_next := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩ with h_S_next
  set u := (⋈|(preTensorCombine_WordStack 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps f)) with h_u
  set C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩)
  simp only [InterleavedWord, InterleavedSymbol, ModuleCode,
    instCodeInterleavableModuleCodeInterleavedSymbol, ModuleCode.moduleInterleavedCode,
    interleavedCodeSet, SetLike.mem_coe, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  -- ⊢ ∀ (k : Fin (2 ^ steps)), uᵀ k ∈ C_next
  intro rowIdx
  -- 2. Setup: Define the specific challenge 'r' corresponding to row index 'rowIdx'
  let r_binary : Fin steps → L := bitsOfIndex rowIdx
  -- 3. Geometric Equivalence:
  -- Show that the `rowIdx`-th row of preTensorCombine is exactly `iterated_fold` of u with challenge r
  -- We rely on Lemma 4.9 (Matrix Form) which states: M_y * vals = iterated_fold(u, r, y)
  let preTensorCombine_Row: S_next → L := preTensorCombine_WordStack 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_i_add_steps (f_i := f) rowIdx
  let rowIdx_binary_folded_Row: S_next → L := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps h_destIdx h_destIdx_le (f := f) (r_challenges := r_binary)
  have h_row_eq_fold : preTensorCombine_Row = rowIdx_binary_folded_Row := by
    funext y
    exact preTensorCombine_row_eq_fold_with_binary_row_challenges 𝔽q β i
      steps h_i_add_steps f rowIdx y
  have h_row_of_u_eq: (uᵀ rowIdx) = preTensorCombine_Row := by rfl
  rw [←h_row_of_u_eq] at h_row_eq_fold
  rw [h_row_eq_fold]
  -- ⊢ rowIdx_binary_folded_Row ∈ C_next (i.e. lhs is of `fold(f, binary_rowIdx_challenges)` form)
  unfold rowIdx_binary_folded_Row
  exact iterated_fold_preserves_BBF_Code_membership 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f) (r_challenges := r_binary)

/-!
--------------------------------------------------------------------------------
   SECTION: THE LIFT INFRASTRUCTURE
   Constructing the inverse map from Interleaved Codewords back to Domain CodeWords
--------------------------------------------------------------------------------
-/


open Code.InterleavedCode in
def getRowPoly (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩)
      ^⋈(Fin (2 ^ steps)))) : Fin (2 ^ steps) → L⦃<2^(ℓ-(i + steps))⦄[X] := fun j => by
  -- 1. Extract polynomials P_j from V_codeword components
  set S_next := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩ with h_S_next
  set C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩ with h_C_next
  let curRow := getRow (show InterleavedCodeword (A := L) (κ := Fin (2 ^ steps)) (ι := S_next) (C := C_next) from V_codeword) j
  have h_V_in_C_next : curRow.val ∈ (C_next) := by
    have h_V_mem := V_codeword.property
    let res := Code.InterleavedCode.getRowOfInterleavedCodeword_mem_code (C := (C_next : Set (S_next → L)))
      (κ := Fin (2 ^ steps)) (ι := S_next) (u := V_codeword) (rowIdx := j)
    exact res
  -- For each j, there exists a polynomial P_j of degree < 2^(ℓ - (i+steps))
  exact getBBF_Codeword_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩) curRow

def getLiftCoeffs (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩)
      ^⋈(Fin (2 ^ steps)))) : Fin (2^(ℓ - i)) → L := fun coeff_idx =>
    -- intertwining novel coeffs of the rows of V_codeword
    -- decompose `coeff_idx = colIdx * 2 ^ steps + rowIdx` as in paper,
      -- i.e. traverse column by column
    let colIdx : Fin (2 ^ (ℓ - (i + steps))) := ⟨coeff_idx.val / (2 ^ steps), by
      apply Nat.div_lt_of_lt_mul;
      rw [← Nat.pow_add];
      convert coeff_idx.isLt using 2; omega
    ⟩
    let rowIdx : Fin (2 ^ steps) := ⟨coeff_idx.val % (2 ^ steps), by
      have h_coeff_idx_lt_two_pow_ℓ_i : coeff_idx.val < 2 ^ (ℓ - i) := by
        exact coeff_idx.isLt
      have h_coeff_idx_mod_two_pow_steps : coeff_idx.val % (2 ^ steps) < 2 ^ steps := by
        apply Nat.mod_lt; simp only [gt_iff_lt, ofNat_pos, pow_pos]
      exact h_coeff_idx_mod_two_pow_steps
    ⟩
    let coeff := getINovelCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i + steps, by omega⟩) (P := (getRowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i steps h_i_add_steps V_codeword) rowIdx) colIdx
    coeff

/-- Given an interleaved codeword `V ∈ C ⋈^ (2^steps)`, this method converts `2^steps` row polys
of `V` into a poly `P ∈ L[X]_(2^(ℓ-i))` that generates the fiber evaluator `g : S⁽ⁱ⁾ → L`
(this `g` produces the RHS vector in equality of **Lemma 4.9**). If we fold this function `g` using
**binary challenges** corresponding to each of the `2^steps` rows of `V`, let's say `j`,
we also folds `P` into the corresponding row polynomial `P_j` of the `j`-th row of `V`
(via **Lemma 4.13, aka iterated_fold_advances_evaluation_poly**). This works as a core engine for
proof of **Lemma 4.21**. -/
def getLiftPoly (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩)
      ^⋈(Fin (2 ^ steps)))) : L⦃<2^(ℓ-i)⦄[X] :=
  ⟨intermediateEvaluationPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
    (getLiftCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps V_codeword), by
      apply Polynomial.mem_degreeLT.mpr
      apply degree_intermediateEvaluationPoly_lt
    ⟩

/-- **Lift Function (Inverse Folding)**
Constructs a function `f` on the domain `S^{(i)}` from an interleaved word `W` on `S^{(i+steps)}`.
For any point `x` in the larger domain, we identify its quotient `y` and its index in the fiber.
We recover the fiber values by applying `M_y⁻¹` to the column `W(y)`.
-/
noncomputable def lift_interleavedCodeword (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩)
      ^⋈(Fin (2 ^ steps)))) :
    BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ := by
  let P : L[X]_(2 ^ (ℓ - ↑i)) := getLiftPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_i_add_steps V_codeword
  -- 3. Define g as evaluation of P
  let g := getBBF_Codeword_of_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) P
  exact g

omit [CharP L 2] [NeZero ℓ] in
/-- **Lemma 4.21 Helper**: Folding the "Lifted" polynomial `g` with binary challenges corresponding
to row index `j ∈ Fin(2^steps)`, results exactly in the `j`-th row polynomial `P_j`.
**Key insight**: **Binary folding** is a **(Row) Selector**
Proof strategy: applying `iterated_fold_advances_evaluation_poly` and
`intermediateEvaluationPoly_from_inovel_coeffs_eq_self`, then arithemetic equality for novel coeffs
computations in both sides. -/
lemma folded_lifted_IC_eq_IC_row_polyToOracleFunc (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i + steps ≤ ℓ) (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i + steps, by omega⟩)^⋈(Fin (2 ^ steps)))) (j : Fin (2 ^ steps)) :
    let g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_i_add_steps V_codeword
    let P_j := (getRowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps
      V_codeword) j
    iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) g (bitsOfIndex j) =
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩) P_j := by
  -- 1. Unfold definitions to expose the underlying polynomials
  -- dsimp only [lift_interleavedCodeword, getLiftPoly]
  simp only
  set g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_i_add_steps V_codeword with h_g
  set P_j := (getRowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps V_codeword) j
  set P_G := getLiftPoly 𝔽q β i steps h_i_add_steps V_codeword with h_P_G -- due to def of `g`
  have h_g : g = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) P_G := by rfl
  -- unfold getLiftPoly at h_P_G
  let novelCoeffs := getLiftCoeffs 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps
    h_i_add_steps V_codeword
  -- have h_P_G_eq: P_G = intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate
    -- (i := ⟨i, by omega⟩) novelCoeffs := by rfl
  let h_fold_g_advances_P_G := iterated_fold_advances_evaluation_poly 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩) (steps := steps)
    (h_i_add_steps := by simp only; omega) (r_challenges := bitsOfIndex j) (coeffs := novelCoeffs)
  simp only [Fin.eta] at h_fold_g_advances_P_G
  conv_lhs at h_fold_g_advances_P_G => -- make it matches the lhs goal
    change iterated_fold 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_i_add_steps := by
      simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (f := g) (bitsOfIndex j)
  conv_lhs => rw [h_fold_g_advances_P_G]
  -- ⊢ polyToOracleFunc 𝔽q β ⟨↑i + steps, ⋯⟩
  --   (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨↑i + steps, ⋯⟩ fun j_1 ↦
  --     ∑ x, multilinearWeight (bitsOfIndex j) x * novelCoeffs ⟨↑j_1 * 2 ^ steps + ↑x, ⋯⟩) =
  -- polyToOracleFunc 𝔽q β ⟨↑i + steps, ⋯⟩ ↑P_j
  have h_P_j_novel_form := intermediateEvaluationPoly_from_inovel_coeffs_eq_self 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩) (P := P_j) (hP_deg := by
        have h_mem := P_j.property
        rw [Polynomial.mem_degreeLT] at h_mem
        exact h_mem )
  conv_rhs => rw [←h_P_j_novel_form]
  -- polyToOracleFunc(intermediateEvaluationPoly(FOLDED novelCoeffs of P))) (via Lemma 4.13)
    -- = polyToOracleFunc(intermediateEvaluationPoly(inovelCoeffs of P_j))
  unfold polyToOracleFunc intermediateEvaluationPoly novelCoeffs
  simp only [map_sum, map_mul, Fin.eta]
  funext y
  congr 1
  apply Finset.sum_congr rfl
  intro x hx_mem_univ
  rw [mul_eq_mul_right_iff]; left
  -- **Arithemetic reasoning**:
  -- ⊢ ∑ x_1, Polynomial.C (multilinearWeight (bitsOfIndex j) x_1) *
          --  Polynomial.C (getLiftCoeffs 𝔽q β i steps ⟨↑x * 2 ^ steps + ↑x_1, ⋯⟩) =
  -- Polynomial.C (getINovelCoeffs 𝔽q β h_ℓ_add_R_rate ⟨↑i + steps, ⋯⟩ (↑P_j) x)
  -- 1. Combine the Ring Homomorphisms to pull C outside the sum
  --    ∑ C(w) * C(v) -> C(∑ w * v)
  simp_rw [←Polynomial.C_mul]
  unfold getINovelCoeffs getLiftCoeffs
  simp only [mul_add_mod_self_right, map_mul]
  -- , ←Polynomial.C_sum]
  -- 2. Use the Indicator Property of multilinearWeight with binary challenges
  --    This logic should ideally be its own lemma: `weight_bits_eq_indicator`
  have h_indicator : ∀ m : Fin (2^steps), multilinearWeight (F := L) (r := bitsOfIndex j)
    (i := m) = if m = j then 1 else 0 := fun m => by
    apply multilinearWeight_bitsOfIndex_eq_indicator (j := m) (k := j)

  simp_rw [h_indicator]
  -- 3. Collapse the Sum using Finset.sum_eq_single
  rw [Finset.sum_eq_single j]
  · -- Case: The Match (x_1 = j)
    simp only [↓reduceIte, map_one, one_mul, Polynomial.C_inj]
    unfold getINovelCoeffs
    simp only
    have h_idx_decomp : (x.val * 2 ^ steps + j.val) / 2^steps = x.val := by
      have h_j_div_2_pow_steps : j.val / 2^steps = 0 := by
        apply Nat.div_eq_of_lt; omega
      rw [mul_comm]
      have h_res := Nat.mul_add_div (m := 2 ^ steps) (x := x.val) (y := j.val) (m_pos := by
        simp only [gt_iff_lt, ofNat_pos, pow_pos])
      simp only [h_j_div_2_pow_steps, add_zero] at h_res
      exact h_res
    congr 1
    · funext k
      congr
      · apply Nat.mod_eq_of_lt; omega
    · simp_rw [h_idx_decomp]
  · -- Case: The Mismatch (x_1 ≠ j)
    intro m _ h_neq
    simp only [h_neq, ↓reduceIte, map_zero, zero_mul]
  · -- Case: Domain (Empty implies false, but we are in Fin (2^steps))
    intro h_absurd
    exfalso; exact h_absurd (Finset.mem_univ j)

omit [CharP L 2] [NeZero ℓ] in
open Code.InterleavedCode in
lemma preTensorCombine_of_lift_interleavedCodeword_eq_self (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i + steps ≤ ℓ)
    (V_codeword : ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩)
      ^⋈(Fin (2 ^ steps)))) :
    let g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      i steps h_i_add_steps V_codeword
    (⋈|(preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps g)) = V_codeword.val := by
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
  let C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩
  set g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    (steps := steps) h_destIdx h_destIdx_le (V_codeword := V_codeword)

  -- **FIRST**,
    -- `∀ j : Fin (2^ϑ), (V_codeword j)` and `fold(g, bitsOfIndex j)` agree identically
        -- over `S^{(i+ϑ)}`
    -- the dotproduct between `M_y's j'th ROW` and `G = g's restriction to the fiber of y`
        -- is actually the result of `fold(G, bitsOfIndex j)`

  have h_agree_with_fold := preTensorCombine_row_eq_fold_with_binary_row_challenges 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps g

  let eq_iff_all_rows_eq := (instInterleavedStructureInterleavedWord (A := L) (κ := Fin (2 ^ steps))
    (ι := S_next)).eq_iff_all_rows_eq (u := ⋈|preTensorCombine_WordStack 𝔽q β (i := i)
      (steps := steps) h_destIdx h_destIdx_le (↑g)) (v := V_codeword.val)
  simp only
  rw [eq_iff_all_rows_eq]
  intro j
  funext (y : S_next) -- compare the cells at (j, y)
  set G := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) (h_i_add_steps := by
    simp only; apply Nat.lt_add_of_pos_right_of_le; omega) (f := g) (y := y)
  simp only [InterleavedWord, Word, InterleavedSymbol, instInterleavedStructureInterleavedWord,
    InterleavedWord.getRowWord, InterleavedWord.getSymbol, transpose_apply, WordStack,
    instInterleavableWordStackInterleavedWord, interleave_wordStack_eq, ModuleCode,
    instCodeInterleavableModuleCodeInterleavedSymbol.eq_1, ModuleCode.moduleInterleavedCode.eq_1,
    interleavedCodeSet.eq_1]
  -- ⊢ preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps (↑g) j = (↑V_codeword)ᵀ j
  unfold preTensorCombine_WordStack
  simp only
  set M_y := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
    h_destIdx h_destIdx_le y
  -- ⊢ (foldMatrix 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ y *ᵥ fiberEvaluations 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ (↑g) y) j
    -- = ↑V_codeword y j
  change (M_y *ᵥ G) j = V_codeword.val y j
  let lhs_eq_fold := h_agree_with_fold j y
  unfold preTensorCombine_WordStack at lhs_eq_fold
  simp at lhs_eq_fold
  rw [lhs_eq_fold]
  -- ⊢ iterated_fold 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ (↑g) (bitsOfIndex j) y = ↑V_codeword y j

  -- **SECOND**, we prove that **the same row polynomial `P_j(X)` is used to generates** bot
    -- `fold(g, bitsOfIndex j)` and `j'th row of V_codeword`

  let curRow := getRow (show InterleavedCodeword (A := L) (κ := Fin (2 ^ steps))
    (ι := S_next) (C := C_next) from V_codeword) j

  let P_j := getRowPoly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps V_codeword j
  let lhs := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ (steps := steps)
    h_destIdx h_destIdx_le (f := g)
    (r_challenges := bitsOfIndex j)
  let rhs := curRow.val
  let generatedRow : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩ :=
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩) (P := P_j)

  have h_left_eq_P_j_gen: lhs = generatedRow := by
    unfold lhs generatedRow -- ⊢ iterated_fold 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ (↑g) (bitsOfIndex j)
      -- = polyToOracleFunc 𝔽q β ⟨↑i + steps, ⋯⟩ ↑P_j
    apply folded_lifted_IC_eq_IC_row_polyToOracleFunc

  have h_right_eq_P_j_eval: rhs = generatedRow := by
    unfold rhs generatedRow
    rw [getBBF_Codeword_poly_spec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨i + steps, by omega⟩) (u := curRow)]; rfl

  conv_lhs => change lhs y
  conv_rhs => change rhs y
  rw [h_left_eq_P_j_gen, h_right_eq_P_j_eval]

/-- TODO: **Lifting Equivalence Lemma**: `lift(preTensorCombine(f)) = f`. -/

def fiberDiff (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩) : Prop :=
  ∃ x, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps (by omega) x = y ∧ f x ≠ g x

/-- **Distance Isomorphism Lemma**
The crucial logic for Lemma 4.21:
Two functions `f, g` differ on a specific fiber `y` IF AND ONLY IF
their tensor-combinations `U, V` differ at the column `y`.
This holds because `M_y` is a bijection. -/
lemma fiberwise_disagreement_isomorphism (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩) :
    fiberDiff 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps f g y ↔
    WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps f) y ≠
    WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps g) y := by
  -- U_y = M_y * f_vals, V_y = M_y * g_vals
  let M_y := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) h_destIdx h_destIdx_le y
  let f_vals := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) h_destIdx h_destIdx_le f y
  let g_vals := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) h_destIdx h_destIdx_le g y

  have h_det : M_y.det ≠ 0 := foldMatrix_det_ne_zero 𝔽q β (i := i) (steps := steps) (h_i := by omega) (y := y)
  constructor
  · -- Forward: Fiber different => Columns different
    intro h_diff
    -- If fiber is different, then vectors f_vals ≠ g_vals
    have h_vec_diff : f_vals ≠ g_vals := by
      rcases h_diff with ⟨x, h_gen_y, h_val_ne⟩ -- h_val_ne : f x ≠ g x
      intro h_eq
      let x_is_fiber_of_y := is_fiber_iff_generates_quotient_point 𝔽q β
        (i := i) (steps := steps) h_destIdx h_destIdx_le
        (x := x) (y := y).mp (by exact id (Eq.symm h_gen_y))
      let x_fiberIdx : Fin (2 ^ steps) :=
        pointToIterateQuotientIndex 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        h_destIdx h_destIdx_le (x := x)
      have h_left_eval : f_vals x_fiberIdx = f x := by
        unfold f_vals fiberEvaluations
        rw [x_is_fiber_of_y]
      have h_right_eval : g_vals x_fiberIdx = g x := by
        unfold g_vals fiberEvaluations
        rw [x_is_fiber_of_y]
      let h_eval_eq := congrFun h_eq x_fiberIdx
      rw [h_left_eval, h_right_eval] at h_eval_eq -- f x = g x
      exact h_val_ne h_eval_eq
    -- M_y is invertible, so M_y * u = M_y * v => u = v. Contrapositive: u ≠ v => M_y * u ≠ M_y * v
    intro h_col_eq
    apply h_vec_diff
    -- ⊢ f_vals = g_vals
    -- h_col_eq: WordStack.getSymbol (preTensorCombine_WordStack ... f) y = WordStack.getSymbol (preTensorCombine_WordStack ... g) y
    -- This means: M_y *ᵥ f_vals = M_y *ᵥ g_vals
    -- Rewrite as: M_y *ᵥ (f_vals - g_vals) = 0
    have h_mulVec_sub_eq_zero : M_y *ᵥ (f_vals - g_vals) = 0 := by
      -- From h_col_eq and the definition of preTensorCombine_WordStack:
      -- WordStack.getSymbol (preTensorCombine_WordStack ... f) y = M_y *ᵥ f_vals
      -- WordStack.getSymbol (preTensorCombine_WordStack ... g) y = M_y *ᵥ g_vals
      have h_f_col : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps f) y = M_y *ᵥ f_vals := by
        ext j
        simp only [WordStack.getSymbol, Matrix.transpose_apply]
        rfl
      have h_g_col : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps g) y = M_y *ᵥ g_vals := by
        ext j
        simp only [WordStack.getSymbol, Matrix.transpose_apply]
        rfl
      -- ⊢ M_y *ᵥ (f_vals - g_vals) = 0
      rw [h_f_col, h_g_col] at h_col_eq
      -- Now h_col_eq: M_y *ᵥ f_vals = M_y *ᵥ g_vals
      rw [Matrix.mulVec_sub]
      -- Goal: M_y *ᵥ f_vals - M_y *ᵥ g_vals = 0
      rw [← h_col_eq]
      -- Goal: M_y *ᵥ f_vals - M_y *ᵥ f_vals = 0
      rw [sub_self]
    -- Apply eq_zero_of_mulVec_eq_zero to get f_vals - g_vals = 0
    have h_sub_eq_zero : f_vals - g_vals = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero h_det h_mulVec_sub_eq_zero -- `usage of M_y's nonsingularity`
    -- Convert to f_vals = g_vals
    exact sub_eq_zero.mp h_sub_eq_zero
  · -- Backward: Columns different => Fiber different
    intro h_col_diff
    by_contra h_fiber_eq
    -- h_fiber_eq: ¬fiberDiff, i.e., ∀ x, iteratedQuotientMap ... x = y → f x = g x
    -- If f and g agree on all points in the fiber of y, then f_vals = g_vals
    have h_vals_eq : f_vals = g_vals := by
      ext idx
      -- f_vals idx = f evaluated at the idx-th point in the fiber of y
      -- g_vals idx = g evaluated at the idx-th point in the fiber of y
      -- We need to show they're equal
      unfold f_vals g_vals fiberEvaluations
      -- fiberEvaluations f y idx = f (qMap_total_fiber ... y idx)
      -- fiberEvaluations g y idx = g (qMap_total_fiber ... y idx)
      let x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        h_destIdx h_destIdx_le (y := y) idx
      -- x is in the fiber of y, so iteratedQuotientMap ... x = y
      have h_x_in_fiber : iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps (by omega) x = y := by
        -- This follows from generates_quotient_point_if_is_fiber_of_y
        have h := generates_quotient_point_if_is_fiber_of_y 𝔽q β (i := i) (steps := steps)
          h_destIdx h_destIdx_le (x := x) (y := y) (hx_is_fiber := by use idx)
        exact h.symm
      -- Since h_fiber_eq says no point in the fiber has f x ≠ g x,
      -- we have f x = g x for all x in the fiber
      have h_fx_eq_gx : f x = g x := by
        -- h_fiber_eq: ¬fiberDiff, which is ¬(∃ x, iteratedQuotientMap ... x = y ∧ f x ≠ g x)
        -- By De Morgan: ∀ x, ¬(iteratedQuotientMap ... x = y ∧ f x ≠ g x)
        -- Which means: ∀ x, iteratedQuotientMap ... x = y → f x = g x
        push_neg at h_fiber_eq
        -- h_fiber_eq is now: ∀ x, iteratedQuotientMap ... x = y → f x = g x
        unfold fiberDiff at h_fiber_eq
        simp only [ne_eq, Subtype.exists, not_exists, not_and, Decidable.not_not] at h_fiber_eq
        let res := h_fiber_eq x (by simp only [SetLike.coe_mem]) h_x_in_fiber
        exact res
      -- Now f_vals idx = f x = g x = g_vals idx
      exact h_fx_eq_gx
    -- If f_vals = g_vals, then M_y *ᵥ f_vals = M_y *ᵥ g_vals
    have h_col_eq : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps f) y =
                    WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps g) y := by
      -- From the forward direction, we know:
      -- WordStack.getSymbol (preTensorCombine_WordStack ... f) y = M_y *ᵥ f_vals
      -- WordStack.getSymbol (preTensorCombine_WordStack ... g) y = M_y *ᵥ g_vals
      have h_f_col : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps f) y = M_y *ᵥ f_vals := by
        ext j
        simp only [WordStack.getSymbol, Matrix.transpose_apply]
        rfl
      have h_g_col : WordStack.getSymbol (preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps g) y = M_y *ᵥ g_vals := by
        ext j
        simp only [WordStack.getSymbol, Matrix.transpose_apply]
        rfl
      rw [h_f_col, h_g_col]
      -- Goal: M_y *ᵥ f_vals = M_y *ᵥ g_vals
      rw [h_vals_eq]
    -- This contradicts h_col_diff
    exact h_col_diff h_col_eq

end Lift_PreTensorCombine

open Classical in
/-- **Proposition 4.20 (Case 1)**:
If f⁽ⁱ⁾ is fiber-wise close to the code, the probability of the bad event is bounded.
The bad event here is: `Δ⁽ⁱ⁾(f⁽ⁱ⁾, f̄⁽ⁱ⁾) ⊄ Δ(fold(f⁽ⁱ⁾), fold(f̄⁽ⁱ⁾))`.
-/
lemma prop_4_20_case_1_fiberwise_close (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    (h_i_add_steps : i + steps ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f_i)) :
    let S_next := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
    let domain_size := Fintype.card S_next
    Pr_{ let r_challenges ←$ᵖ (Fin steps → L) }[
        -- The definition of foldingBadEvent under the "then" branch of h_close
        let f_bar_i := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          ⟨i, by omega⟩ f_i
          (UDRClose_of_fiberwiseClose 𝔽q β i steps h_i_add_steps f_i h_close)
        let folded_f_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
          steps (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f_i r_challenges
        let folded_f_bar_i := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
          steps (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f_bar_i r_challenges
        ¬ (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f_i f_bar_i ⊆
           disagreementSet 𝔽q β ⟨i + steps, by omega⟩ folded_f_i folded_f_bar_i)
    ] ≤ ((steps * domain_size) / Fintype.card L) := by
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
  let L_card := Fintype.card L
  -- 1. Setup Definitions
  let f_bar_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ :=
    UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i.val, by omega⟩)
    (f := f_i) (h_within_radius := UDRClose_of_fiberwiseClose 𝔽q β i steps h_i_add_steps f_i h_close)
  let Δ_fiber : Set (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩) :=
    fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f_i f_bar_i
  -- We apply the Union Bound over `y ∈ Δ_fiber`
    -- `Pr[ ∃ y ∈ Δ_fiber, y ∉ Disagreement(folded) ] ≤ ∑ Pr[ y ∉ Disagreement(folded) ]`
  have h_union_bound :
    Pr_{ let r ←$ᵖ (Fin steps → L) }[
      ¬(Δ_fiber ⊆ disagreementSet 𝔽q β ⟨i + steps, by omega⟩
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f_i r)
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f_bar_i r))
    ] ≤ ∑ y ∈ Δ_fiber.toFinset,
        Pr_{ let r ←$ᵖ (Fin steps → L) }[
            -- The condition y ∉ Disagreement(folded) implies folded values are equal at y
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f_i r) y =
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f_bar_i r) y
        ] := by
      -- Standard probability union bound logic
      -- Convert probability to cardinality ratio for the Union Bound
      rw [prob_uniform_eq_card_filter_div_card]
      simp_rw [prob_uniform_eq_card_filter_div_card]
      simp only [ENNReal.coe_natCast, Fintype.card_pi, prod_const, Finset.card_univ,
        Fintype.card_fin, cast_pow, ENNReal.coe_pow]
      set left_set : Finset (Fin steps → L) :=
        Finset.univ.filter fun r =>
          ¬(Δ_fiber ⊆
            disagreementSet 𝔽q β ⟨i + steps, by omega⟩ (iterated_fold 𝔽q β ⟨i, by omega⟩ steps
              (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f_i r)
              (iterated_fold 𝔽q β ⟨↑i, by omega⟩ steps
              (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f_bar_i r))

      set right_set :
          (x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩) →
            Finset (Fin steps → L) :=
        fun x =>
          (Finset.univ.filter fun r =>
            iterated_fold 𝔽q β ⟨↑i, by omega⟩ steps
                (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
                f_i r x =
              iterated_fold 𝔽q β ⟨↑i, by omega⟩ steps
                (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
                f_bar_i r x)
      conv_lhs =>
        change _ * ((Fintype.card L : ENNReal) ^ steps)⁻¹
        rw [mul_comm]
      conv_rhs =>
        change
          ∑ y ∈ Δ_fiber.toFinset,
            ((#(right_set y) : ENNReal) * ((Fintype.card L : ENNReal) ^ steps)⁻¹)
      conv_rhs =>
        simp only [mul_comm]
        rw [←Finset.mul_sum]
      -- ⊢ (↑(Fintype.card L) ^ steps)⁻¹ * ↑(#left_set) ≤ (↑(Fintype.card L) ^ steps)⁻¹ * ∑ i ∈ Δ_fiber.toFinset, ↑(#(right_set i))
      let left_le_right_if := (ENNReal.mul_le_mul_left (a := ((Fintype.card L : ENNReal) ^ steps)⁻¹) (b := (#left_set)) (c := ∑ i ∈ Δ_fiber.toFinset, (#(right_set i))) (h0 := by simp only [ne_eq,
        ENNReal.inv_eq_zero, ENNReal.pow_eq_top_iff, ENNReal.natCast_ne_top, false_and,
        not_false_eq_true]) (hinf := by simp only [ne_eq, ENNReal.inv_eq_top, pow_eq_zero_iff',
          cast_eq_zero, Fintype.card_ne_zero, false_and, not_false_eq_true])).mpr
      apply left_le_right_if

      -- ⊢ ↑(#left_set) ≤ ∑ i ∈ Δ_fiber.toFinset, ↑(#(right_set i))

      -- 1. Prove the subset relation: left_set ⊆ ⋃_{y ∈ Δ} right_set y
      -- This formally connects the failure condition (∃ y, agree) to the union of agreement sets.
      have h_subset : left_set ⊆ Δ_fiber.toFinset.biUnion right_set := by
        intro r hr
        -- Unpack membership in left_set: r is bad if Δ_fiber ⊈ disagreementSet
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, left_set] at hr
        rw [Set.not_subset] at hr
        rcases hr with ⟨y, hy_mem, hy_not_dis⟩
        -- We found a y ∈ Δ_fiber where they do NOT disagree (i.e., they agree)
        rw [Finset.mem_biUnion]
        use y
        constructor
        · exact Set.mem_toFinset.mpr hy_mem
        · -- Show r ∈ right_set y (which is defined as the set of r where they agree at y)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, right_set]
          -- hy_not_dis is ¬(folded_f_i y ≠ folded_f_bar_i y) ↔ folded_f_i y = folded_f_bar_i y
          simp only [disagreementSet, ne_eq, coe_filter, mem_univ, true_and, Set.mem_setOf_eq,
            Decidable.not_not] at hy_not_dis
          exact hy_not_dis

      -- 2. Apply cardinality bounds (Union Bound)
      calc
        (left_set.card : ENNReal)
        _ ≤ (Δ_fiber.toFinset.biUnion right_set).card := by
          -- Monotonicity of measure/cardinality: A ⊆ B → |A| ≤ |B|
          gcongr
        _ ≤ ∑ i ∈ Δ_fiber.toFinset, (right_set i).card := by
          -- Union Bound: |⋃ S_i| ≤ ∑ |S_i|
          -- push_cast moves the ENNReal coercion inside the sum
          push_cast
          let h_le_in_Nat := Finset.card_biUnion_le (s := Δ_fiber.toFinset) (t := right_set)
          norm_cast
        _ = _ := by push_cast; rfl
  apply le_trans h_union_bound
  -- Now bound the individual probabilities using Schwartz-Zippel
  have h_prob_y : ∀ y ∈ Δ_fiber,
    Pr_{ let r ←$ᵖ (Fin steps → L) }[
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f_i r) y =
        (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f_bar_i r) y
    ] ≤ (steps) / L_card := by
    intro y hy
    -- 1. Apply Lemma 4.9 (iterated_fold_eq_matrix_form) to express the equality as a matrix eq.
    --    Equality holds iff Tensor(r) * M_y * (f - f_bar)|_fiber = 0.
    -- 2. Define the polynomial P(r) = Tensor(r) * w, where w = M_y * (vals_f - vals_f_bar).
    -- 3. Show w ≠ 0:
    --      a. vals_f - vals_f_bar ≠ 0 because y ∈ Δ_fiber (definitions).
    --      b. M_y is nonsingular (Lemma 4.9 / Butterfly structure).
    -- 4. Apply prob_schwartz_zippel_mv_polynomial to P(r).
    --      degree(P) = steps.
    -- 1. Apply Lemma 4.9 to express folding as Matrix Form
    -- Equality holds iff [Tensor(r)] * [M_y] * [f - f_bar] = 0
    let vals_f : Fin (2 ^ steps) → L := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      h_destIdx h_destIdx_le f_i y
    let vals_f_bar : Fin (2 ^ steps) → L := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      h_destIdx h_destIdx_le f_bar_i y
    let v_diff : Fin (2 ^ steps) → L := vals_f - vals_f_bar

    -- 2. Show `v_diff ≠ 0` because `y ∈ Δ_fiber`, this is actually by definition of `Δ_fiber`.
    have hv_ne_zero : v_diff ≠ 0 := by
      unfold v_diff
      have h_exists_diff_point: ∃ x: Fin (2 ^ steps), vals_f x ≠ vals_f_bar x := by
        dsimp only [fiberwiseDisagreementSet, ne_eq, Δ_fiber] at hy
        -- ∃ x, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x = y ∧ f_i x ≠ f_bar_i x
        simp only [Subtype.exists, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy
        -- rcases hy with ⟨xL, h_quot, h_ne⟩
        rcases hy with ⟨xL, h_prop_xL⟩
        rcases h_prop_xL with ⟨xL_mem_sDomain, h_quot, h_ne⟩
        set xSDomain : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) := ⟨xL, xL_mem_sDomain⟩
        let x_is_fiber_of_y :=
          is_fiber_iff_generates_quotient_point 𝔽q β (i := i) (steps := steps) h_destIdx h_destIdx_le
          (x := xSDomain) (y := y).mp (by exact id (Eq.symm h_quot))
        let x_fiberIdx : Fin (2 ^ steps) := pointToIterateQuotientIndex 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          h_destIdx h_destIdx_le (x := xSDomain)
        use x_fiberIdx
        have h_left_eval : vals_f x_fiberIdx = f_i xSDomain := by
          unfold vals_f fiberEvaluations
          rw [x_is_fiber_of_y]
        have h_right_eval : vals_f_bar x_fiberIdx = f_bar_i xSDomain := by
          unfold vals_f_bar fiberEvaluations
          rw [x_is_fiber_of_y]
        rw [h_left_eval, h_right_eval]
        exact h_ne
      by_contra h_eq_zero
      rw [funext_iff] at h_eq_zero
      rcases h_exists_diff_point with ⟨x, h_ne⟩
      have h_eq: vals_f x = vals_f_bar x := by
        have res := h_eq_zero x
        simp only [Pi.sub_apply, Pi.zero_apply] at res
        rw [sub_eq_zero] at res
        exact res
      exact h_ne h_eq

    -- 3. M_y is nonsingular (from Lemma 4.9 context/properties of AdditiveNTT)
    let M_y := foldMatrix 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      h_destIdx h_destIdx_le  y
    have hMy_det_ne_zero : M_y.det ≠ 0 := by
      apply foldMatrix_det_ne_zero 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
        (h_i := by omega) (y := y)

    -- 4. w = M_y * v_diff is non-zero
    let w := M_y *ᵥ v_diff
    have hw_ne_zero : w ≠ 0 := by
      intro h
      exact hv_ne_zero (by exact Matrix.eq_zero_of_mulVec_eq_zero hMy_det_ne_zero h)

    -- 5. Construct the polynomial P(r) = Tensor(r) ⬝ w
    -- This is a multilinear polynomial of degree `steps`
    -- Tensor(r)_k corresponds to the Lagrange basis polynomial evaluated at r
    let P : MvPolynomial (Fin steps) L :=
        ∑ k : Fin (2^steps), (MvPolynomial.C (w k)) * (MvPolynomial.eqPolynomial (r := bitsOfIndex k))

    have hP_eval : ∀ r, P.eval r = (challengeTensorExpansion steps r) ⬝ᵥ w := by
      intro r
      simp only [P, MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
      rw [dotProduct]
      apply Finset.sum_congr rfl
      intro k hk_univ
      conv_lhs => rw [mul_comm]
      congr 1
      -- evaluation of Lagrange basis matches tensor expansion
      -- ⊢ (MvPolynomial.eval r) (eqPolynomial (bitsOfIndex k)) = challengeTensorExpansion steps r k

      -- Unfold definitions to expose the product structure
      unfold eqPolynomial singleEqPolynomial bitsOfIndex challengeTensorExpansion multilinearWeight
      rw [MvPolynomial.eval_prod] -- prod structure of `eqPolynomial`
      -- Now both sides have form `∏ (j : Fin steps), ...`
      apply Finset.prod_congr rfl
      intro j _
      -- Simplify polynomial evaluation
      simp only [MonoidWithZeroHom.map_ite_one_zero, ite_mul, one_mul, zero_mul,
        MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_sub, map_one,
        MvPolynomial.eval_X]
      split_ifs with h_bit
      · -- Case: Bit is 1
        simp only [sub_self, zero_mul, MvPolynomial.eval_X, zero_add]
      · -- Case: Bit is 0
        simp only [sub_zero, one_mul, map_zero, add_zero]

    have hP_nonzero : P ≠ 0 := by
      -- Assume P = 0 for contradiction
      intro h_P_zero
      -- Since w ≠ 0, there exists some index k such that w k ≠ 0
      rcases Function.ne_iff.mp hw_ne_zero with ⟨k, hk_ne_zero⟩

      -- Let r_k be the bit-vector corresponding to index k
      let r_k := bitsOfIndex (L := L) k

      -- If P = 0, then P(r_k) must be 0
      have h_eval_zero : MvPolynomial.eval r_k P = 0 := by
        rw [h_P_zero]; simp only [map_zero]

      -- On the other hand, we proved P(r) = Tensor(r) ⬝ w
      rw [hP_eval r_k] at h_eval_zero

      -- Key Property: Tensor(r_k) is the indicator vector for k.
      -- Tensor(r_k)[j] = 1 if j=k, 0 if j≠k.
      have h_tensor_k : ∀ j, (challengeTensorExpansion steps r_k) j = if j = k then 1 else 0 := by
        intro j
        rw [challengeTensorExpansion_bitsOfIndex_is_eq_indicator (L := L) (n := steps) (k := k)]

      -- Thus the dot product is exactly w[k]
      rw [dotProduct, Finset.sum_eq_single k] at h_eval_zero
      · simp only [h_tensor_k, if_true, one_mul] at h_eval_zero
        exact hk_ne_zero h_eval_zero
      · -- Other terms are zero
        intro j _ h_ne
        simp [h_tensor_k, h_ne]
      · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff] -- Case where index k is not in univ (impossible for Fin n)

    have hP_deg : P.totalDegree ≤ steps := by
      -- Use the correct lemma from the list: sum degree ≤ d if all terms degree ≤ d
      apply MvPolynomial.totalDegree_finsetSum_le
      intro k _
      -- Bound degree of each term: deg(C * eqPoly) ≤ deg(C) + deg(eqPoly) = 0 + deg(eqPoly)
      apply le_trans (MvPolynomial.totalDegree_mul _ _)
      simp only [MvPolynomial.totalDegree_C, zero_add]

      -- Bound degree of eqPolynomial (product of linear terms)
      unfold eqPolynomial
      -- deg(∏ f) ≤ ∑ deg(f)
      apply le_trans (MvPolynomial.totalDegree_finset_prod _ _)

      -- The sum of `steps` terms, each of degree ≤ 1
      trans ∑ (i : Fin steps), 1
      · apply Finset.sum_le_sum
        intro i _
        -- Check degree of singleEqPolynomial: r*X + (1-r)*(1-X)
        unfold singleEqPolynomial
        -- deg(A + B) ≤ max(deg A, deg B)
        apply (MvPolynomial.totalDegree_add _ _).trans
        rw [max_le_iff]
        constructor
        · -- deg(C * X) ≤ 1
          apply (MvPolynomial.totalDegree_mul _ _).trans
          -- simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
          -- ⊢ (1 - MvPolynomial.C (bitsOfIndex k i)).totalDegree + (1 - MvPolynomial.X i).totalDegree ≤ 1
          calc
            _ ≤ ((1 : L[X Fin steps]) - MvPolynomial.X i).totalDegree := by
              have h_left_le := MvPolynomial.totalDegree_sub_C_le (p := (1 : L[X Fin steps])) (r := bitsOfIndex k i)
              simp only [totalDegree_one] at h_left_le -- (1 - C (bitsOfIndex k i)).totalDegree ≤ 0
              omega
            _ ≤ max ((1 : L[X Fin steps]).totalDegree) ((MvPolynomial.X (R := L) i).totalDegree) := by
              apply MvPolynomial.totalDegree_sub
            _ = _ := by
              simp only [totalDegree_one, totalDegree_X, _root_.zero_le, sup_of_le_right]
        · -- deg(C * (X)) ≤ 1
          apply (MvPolynomial.totalDegree_mul _ _).trans
          simp only [MvPolynomial.totalDegree_C, zero_add]
          -- ⊢ (MvPolynomial.X i).totalDegree ≤ 1
          simp only [totalDegree_X, le_refl]
      · simp only [sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, le_refl]
    -- 6. Apply Schwartz-Zippel using Pr_congr to switch the event
    rw [Pr_congr (Q := fun r => MvPolynomial.eval r P = 0)]
    · apply prob_schwartz_zippel_mv_polynomial P hP_nonzero hP_deg
    · intro r
      -- Show that (Folding Eq) ↔ (P(r) = 0)
      rw [iterated_fold_eq_matrix_form 𝔽q β h_destIdx h_destIdx_le, iterated_fold_eq_matrix_form 𝔽q β h_destIdx h_destIdx_le]
      -- Expand the dot product logic:
      unfold localized_fold_matrix_form single_point_localized_fold_matrix_form
      rw [hP_eval]
      rw [Matrix.dotProduct_mulVec]
      simp only
      -- ⊢ challengeTensorExpansion steps r ᵥ* foldMatrix 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ y ⬝ᵥ fiberEvaluations 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ f_i y =
      --     challengeTensorExpansion steps r ⬝ᵥ
      --       foldMatrix 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ y *ᵥ fiberEvaluations 𝔽q β ⟨↑i, ⋯⟩ steps ⋯ f_bar_i y ↔
      --   challengeTensorExpansion steps r ⬝ᵥ w = 0
      rw [←sub_eq_zero]
      -- Transform LHS: u ⬝ (M * a) - u ⬝ (M * b) = u ⬝ (M * a - M * b)
      rw [←Matrix.dotProduct_mulVec]
      rw [←dotProduct_sub]
      -- Transform inner vector: M * a - M * b = M * (a - b)
      rw [←Matrix.mulVec_sub]
      -- Substitute definition of w: w = M * (vals_f - vals_f_bar)
      -- Note: v_diff was defined as vals_f - vals_f_bar
      -- And w was defined as M_y *ᵥ v_diff

  -- Sum the bounds: |Δ_fiber| * (steps / |L|)
  -- Since |Δ_fiber| ≤ |S_next|, this is bounded by |S_next| * steps / |L|
  have h_card_fiber : Δ_fiber.toFinset.card ≤ Fintype.card S_next :=
    Finset.card_le_univ Δ_fiber.toFinset

  calc
    _ ≤ ∑ y ∈ Δ_fiber.toFinset, (steps : ENNReal)  / L_card := by
        apply Finset.sum_le_sum
        intro y hy -- hy : y ∈ Δ_fiber.toFinset
        let res := h_prob_y y (by exact Set.mem_toFinset.mp hy)
        exact res
    _ = (Δ_fiber.toFinset.card) * (steps / L_card) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card S_next) * (steps / L_card) := by
        gcongr
    _ = (steps * Fintype.card S_next) / L_card := by
      ring_nf
      conv_rhs => rw [mul_div_assoc]

open Code.InterleavedCode in
/-- **Lemma 4.21** (Interleaved Distance Preservation):
If `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) ≥ d_{i+ϑ} / 2` (`f` is fiber-wise far wrt UDR),
then `d^{2^ϑ}( (f_j⁽ⁱ⁺ϑ⁾)_{j=0}^{2^ϑ - 1}, C^{(i+ϑ)^{2^ϑ}} ) ≥ d_{i+ϑ} / 2`
  (i.e. interleaved distance ≥ UDR distance).
* **Main Idea of Proof:** For an ARBITRARY interleaved codeword `(g_j⁽ⁱ⁺ϑ⁾)`,
a "lift" `g⁽ⁱ⁾ ∈ C⁽ⁱ⁾` is constructed. It's shown that `g⁽ⁱ⁾` relates to `(g_j⁽ⁱ⁺ϑ⁾)` (via
folding with basis vectors as challenges) similarly to how `f⁽ⁱ⁾` relates to `(f_j⁽ⁱ⁺ϑ⁾)` (via
Lemma 4.9 and matrix `M_y`). Since `f⁽ⁱ⁾` is far from `g⁽ⁱ⁾` on many fibers (by hypothesis), and
`M_y` is invertible, the columns `(f_j⁽ⁱ⁺ϑ⁾(y))` and `(g_j⁽ⁱ⁺ϑ⁾(y))` must differ for these `y`,
establishing the distance for the interleaved words. -/
lemma lemma_4_21_interleaved_word_UDR_far (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    (h_i_add_steps : i + steps ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_far : ¬fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      h_destIdx h_destIdx_le (f := f_i)) :
    let U := preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps f_i
    let C_next : Set (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩ → L) :=
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩
    ¬(jointProximityNat (C := C_next) (u := U) (e := Code.uniqueDecodingRadius (C := C_next))) := by

  -- 1. Setup variables and definitions
  let m := 2^steps
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
  let C : Set (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ → L) :=
      (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  let C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩
  let C_int := C_next ^⋈ (Fin m)
  let U_wordStack := preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps f_i
  let U_interleaved : InterleavedWord L (Fin m) S_next := ⋈|U_wordStack
  let d_next := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i + steps, by omega⟩)
  let e_udr := Code.uniqueDecodingRadius (C := (C_next : Set (S_next → L)))

  -- 2. Analyze the "Far" hypothesis
  -- h_far : ¬(2 * fiberwiseDistance < d_next) ↔ 2 * fiberwiseDistance ≥ d_next
  -- This means for ANY g ∈ C^(i), the number of fiber disagreements is ≥ d_next/2.
  have h_fiber_dist_ge : ∀ g : BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩,
      2 * (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f_i g).card ≥ d_next := by
    -- Expand negation of fiberwiseClose definition
    intro g
    -- 1. Unwrap the "Far" hypothesis
    -- "Not Close" means 2 * min_dist ≥ d_next
    unfold fiberwiseClose at h_far
    rw [not_lt] at h_far

    -- 2. Set up the set of all distances
    let dist_set := (fun (g' : C) =>
      (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f_i g').card) '' Set.univ

    -- 3. Show that the specific g's distance is >= the minimum distance
    -- We use `csInf_le` which says inf(S) ≤ x for any x ∈ S (provided S is bounded below)
    have h_min_le_g : fiberwiseDistance 𝔽q β i steps h_i_add_steps f_i ≤
        (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f_i g).card := by
      apply csInf_le
      -- S must be bounded below (0 is a lower bound for Nat)
      · use 0
        rintro _ ⟨_, _, rfl⟩
        simp only [_root_.zero_le]
      -- S must be nonempty (g exists)
      · use g
        simp only [Set.mem_univ, true_and]
        rfl

    -- 4. Transitivity: d_next ≤ 2 * min ≤ 2 * specific
    calc
      d_next ≤ 2 * fiberwiseDistance 𝔽q β i steps h_i_add_steps f_i := by
        norm_cast at h_far
      _ ≤ 2 * (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f_i g).card := by
        let res := Nat.mul_le_mul_left (k := (2 : ℕ)) (h := (h_min_le_g))
        exact res

  -- 3. Proof by Contradiction
  -- Assume U is close to C_int (distance ≤ e_udr).
  simp only
  intro h_U_close -- Proof by Contradiction: Assume U is UDR-close to C_int.

  -- By definition of jointProximityNat, this means U is e_udr-close to C_int.
  -- Since C_int is nonempty, there exists a closest codeword V ∈ C_int.
  obtain ⟨V_codeword, h_dist_U_V⟩ := jointProximityNat_iff_closeToInterleavedCodeword
    (u := U_wordStack) (e := e_udr) (C := C_next) |>.mp h_U_close

  -- 4. Construct the "Lifted" Codeword g
  -- We claim there exists a g ∈ C^(i) such that applying `preTensorCombine_WordStack` to g yields V.
  -- This essentially inverses the folding operation. M_y is invertible, so we can recover
  -- the fiber evaluations of g from the columns of V.
  -- The algebraic properties of Binius ensure this reconstructed g is a valid codeword in C^(i).
  let g := lift_interleavedCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps V_codeword
  have h_g_is_lift_of_V : (⋈|preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps ↑g)
    = V_codeword.val := by
    apply preTensorCombine_of_lift_interleavedCodeword_eq_self 𝔽q β

  -- 5. Equivalence of Disagreements via Non-Singular M_y
  -- We show that U and V differ at column y iff f_i and g differ on the CORRESPONDING fiber of y.
  -- This relies on U_y = M_y * f_fiber and V_y = M_y * g_fiber.
  have h_disagreement_equiv : ∀ y : S_next,
      (∃ x, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps (by omega) x = y ∧ f_i x ≠ g.val x) ↔
      getSymbol U_interleaved y ≠ getSymbol V_codeword y := by
    intro y
    let res := fiberwise_disagreement_isomorphism 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f_i) (g := g) (y := y)
    unfold fiberDiff at res
    rw [res]
    have h_col_U_y_eq : (preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps f_i).getSymbol y
      = getSymbol U_interleaved y := by rfl
    have h_col_V_y_eq : (preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps g.val).getSymbol y
      = getSymbol V_codeword y := by
      have h_get_symbol_eq : (preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps
        (g.val)).getSymbol y = getSymbol (⋈|preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps ↑g) y := by rfl
      rw [h_get_symbol_eq]
      rw [h_g_is_lift_of_V]
      -- ⊢ getSymbol (↑V_codeword) y = getSymbol V_codeword y (lhs is I(nterleaved) word, rhs is IC)
      rfl
    rw [h_col_U_y_eq, h_col_V_y_eq]

  -- 6. Connect Distances
  -- The Hamming distance Δ₀(U, V) is exactly the number of columns where they differ.
  -- By the equivalence above, this is exactly the size of `fiberwiseDisagreementSet f_i g`.
  have h_dist_eq : Δ₀(U_interleaved, V_codeword.val) ≥ (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f_i g).card := by
    -- Use h_disagreement_equiv and definition of Hamming distance / fiberwiseDisagreementSet
    -- We prove equality, which implies ≥
    apply le_of_eq
    -- Definition of Hamming distance is count of {y | U y ≠ V y}
    unfold hammingDist
    -- Definition of fiberwiseDisagreementSet is {y | ∃ x ∈ Fiber(y), f x ≠ g x}
    unfold fiberwiseDisagreementSet
    -- We want to show card {y | U y ≠ V y} = card {y | fiber_diff }
    -- It suffices to show the sets are equal.
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- Apply the equivalence we proved in step 5
    rw [h_disagreement_equiv]
    -- The LHS of h_disagreement_equiv matches the RHS of our goal here.
    -- The RHS of h_disagreement_equiv matches the LHS of our goal here.
    -- Just need to handle the `InterleavedWord` wrapper
    rfl

  -- 7. Contradiction Algebra
  -- We have:
  -- (1) 2 * dist(U, V) ≤ 2 * e_udr (by assumption h_U_close)
  -- (2) 2 * e_udr < d_next (by definition of UDR)
  -- (3) 2 * card(disagreement f g) ≥ d_next (by h_far hypothesis applied to g)
  -- (4) dist(U, V) = card(disagreement f g) (by h_dist_eq)
  -- Combining (3) and (4): 2 * dist(U, V) ≥ d_next
  -- Combining (1) and (2): 2 * dist(U, V) < d_next
  -- Contradiction.

  have h_ineq_1 : ¬(2 * (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f_i g).card < d_next) := by
    simp only [not_lt, h_fiber_dist_ge (g := ⟨g, by simp only [SetLike.coe_mem]⟩)]

  have h_ineq_2 : 2 * (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f_i g).card < d_next := by
    calc
      2 * (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f_i g).card
      _ ≤ 2 * Δ₀(U_interleaved, V_codeword.val) := by
        omega
      _ ≤ 2 * e_udr := by
      -- {n m : Nat} (k : Nat) (h : n ≤ m) : n * k ≤ m * k :=
        let res := Nat.mul_le_mul_left (k := 2) (h := h_dist_U_V)
        exact res
      _ < d_next := by
        -- ⊢ 2 * e_udr < d_next
        letI : NeZero (‖(C_next : Set (S_next → L))‖₀) := NeZero.of_pos (by
          simp only; unfold C_next;
          simp_rw [BBF_CodeDistance_eq (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := ⟨i + steps, by omega⟩)]
          -- ⊢ 0 < 2 ^ (ℓ + 𝓡 - (↑i + steps)) - 2 ^ (ℓ - (↑i + steps)) + 1
          omega
        )
        let res := Code.UDRClose_iff_two_mul_proximity_lt_d_UDR
          (C := (C_next : Set (S_next → L))) (e := e_udr).mp (by omega)
        exact res

  exact h_ineq_1 h_ineq_2

lemma prop_4_20_case_2_fiberwise_far (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    (h_i_add_steps : i + steps ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (h_far : ¬fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      h_destIdx h_destIdx_le (f := f_i)) :
    let next_domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩)
    Pr_{ let r ←$ᵖ (Fin steps → L) }[
      let f_next := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
        (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) f_i r
      UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩) f_next
    ] ≤ ((steps * next_domain_size) / Fintype.card L) := by
    -- This requires mapping the fiberwise distance to the interleaved code distance
    -- and applying the tensor product proximity gap results from DG25.lean.
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
  let L_card := Fintype.card L
  let m := 2^steps
  -- 1. Construct the interleaved word U from f_i
  -- U is a matrix of size m x |S_next|, where row j corresponds to the j-th fiber index.
  let U : WordStack L (Fin m) S_next :=
    preTensorCombine_WordStack 𝔽q β i steps h_i_add_steps f_i
  -- 2. Translate Fiber-wise Distance to Interleaved Distance
  -- The fiberwise distance is exactly the minimum Hamming distance between
  -- the columns of U (viewed as vectors in L^m) and the code C^m (interleaved).
  -- Actually, based on Def 4.15/4.16, fiberwiseDistance is the distance of f_i to C_i
  -- but viewed through the fibers. This corresponds to the distance of U to C_next^m.
  let C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩
  let C_interleaved := C_next ^⋈ (Fin m)
  set d_next := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i + steps, by omega⟩)
  -- 3. Apply Tensor Gap Theorem (Contrapositive)
  -- Theorem 3.6 / Corollary 3.7 states:
  -- If Pr[ multilinearCombine(U, r) is close ] > ε/|L|, then U is close to C_int.
  -- Contrapositive: If U is FAR from C_int, then Pr[ multilinearCombine(U, r) is close ] ≤ ε/|L|.
  -- We identify "close" as distance ≤ e, where e = floor((d_next - 1) / 2).
  let e_prox := (d_next - 1) / 2
  -- Check that "far" hypothesis implies "not close"
  -- h_U_far says 2*dist ≥ d_next.
  -- "Close" means dist ≤ e_prox = (d_next - 1)/2 < d_next/2.
  -- So U is strictly greater than e_prox distance away.
  have h_U_not_UDR_close : ¬ (jointProximityNat (u := U) (e := e_prox) (C := C_next)) := by
    apply lemma_4_21_interleaved_word_UDR_far 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps) h_destIdx h_destIdx_le (f_i := f_i) (h_far := h_far)

  -- The epsilon for RS codes / Tensor Gaps is typically |S_next| * steps (or similar).
  -- In DG25 Cor 3.7, ε = |S_next|. The bound is ϑ * ε / |L|.
  let ε_gap := Fintype.card S_next

  -- Apply the Tensor Gap Theorem (Corollary 3.7 for RS codes or Theorem 3.6 generic)
  have h_prob_bound :
    Pr_{ let r ←$ᵖ (Fin steps → L) }[ Δ₀(multilinearCombine U r, C_next) ≤ e_prox ]
    ≤ (steps * ε_gap) / L_card := by
    -- Apply contrapositive of h_tensor_gap applied to U
    by_contra h_prob_gt_bound
    let α := Embedding.subtype fun (x : L) ↦ x ∈ S_next
    let C_i_plus_steps := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + steps, by omega⟩
    let RS_i_plus_steps := ReedSolomon.code α (2^(ℓ - (i+steps)))

    letI : Nontrivial (RS_i_plus_steps) := ReedSolomonCode.instNontrivial

    let h_tensor_gap := reedSolomon_multilinearCorrelatedAgreement_Nat (A := L) (ι := S_next)
      (α := α)
      (k := 2^(ℓ - (i+steps)))
      (hk := by
        rw [sDomain_card, hF₂.out]
        apply Nat.pow_le_pow_right (hx := by omega)
        · simp only [tsub_le_iff_right]; omega
        · simp only; apply Nat.lt_add_of_pos_right_of_le; omega
      )
      (e := e_prox) (he := by exact Nat.le_refl _)
      (ϑ := steps) (hϑ_gt_0 := by exact Nat.pos_of_neZero steps)
    -- 3. Apply the theorem to our specific word U
    -- This concludes "U is close" (jointProximityNat)
    let h_U_UDR_close : jointProximityNat (C := C_i_plus_steps) U e_prox :=
      h_tensor_gap U (by
      rw [ENNReal.coe_natCast]
      rw [not_le] at h_prob_gt_bound
      exact h_prob_gt_bound
    )
    exact h_U_not_UDR_close h_U_UDR_close
  -- 4. Connect Folding to Multilinear Combination
  -- Show that `iterated_fold` is exactly `multilinearCombine` of `U`
  -- Lemma 4.9 (iterated_fold_eq_matrix_form) essentially establishes this connection
  -- multilinearCombine U r = Tensor(r) ⬝ U = iterated_fold f r
  have h_fold_eq_combine : ∀ r,
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ (steps := steps) h_destIdx h_destIdx_le f_i r) =
    multilinearCombine U r := by
    intro r
    ext y
    rw [iterated_fold_eq_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f_i) (r_challenges := r)]
    unfold localized_fold_matrix_form single_point_localized_fold_matrix_form multilinearCombine
    simp only [dotProduct, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro (rowIdx : Fin (2^steps)) h_rowIdx_univ
    rfl
  -- 5. Conclusion
  -- The event inside the probability is: 2 * dist(folded, C_next) < d_next
  -- This is equivalent to dist(folded, C_next) ≤ (d_next - 1) / 2 = e_prox
  rw [Pr_congr (Q := fun r => Δ₀(multilinearCombine U r, C_next) ≤ e_prox)]
  · exact h_prob_bound
  · intro r
    rw [←h_fold_eq_combine]
    rw [UDRClose_iff_within_UDR_radius]
    have h_e_prox_def : e_prox = Code.uniqueDecodingRadius
      (C := (C_next : Set (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩ → L))) := by rfl
    rw [h_e_prox_def]

/-!
### Soundness Lemmas (4.20 - 4.25)
-/

open Classical in
/-- **Proposition 4.20** (Bound on Bad Folding Event):
The probability (over random challenges `r`) of the bad folding event is bounded.
Bound: `μ(Eᵢ) ≤ ϑ ⋅ |S⁽ⁱ⁺ϑ⁾| / |L|` (where `μ(R) = Pr_{ let r ←$ᵖ (Fin steps → L) }[ R ]`)
**Case 1: Fiber-wise close** =>
  `μ(Δ⁽ⁱ⁾(f⁽ⁱ⁾, f̄⁽ⁱ⁾) ⊄ Δ_folded_disagreement) ≤ steps · |S⁽ⁱ⁺steps⁾| / |L|`
Proof strategy:
- Show that `∀ y ∈ Δ_fiber, μ(y ∉ Δ_folded_disagreement) ≤ steps / |L|`
- Apply the Union Bound over `y ∈ Δ_fiber`
**Case 2: Fiber-wise far** =>
  μ(`d(fold(f⁽ⁱ⁾, rᵢ', ..., rᵢ₊steps₋₁'), C⁽ⁱ⁺steps⁾) < dᵢ₊steps / 2`) ≤ steps · |S⁽ⁱ⁺steps⁾| / |L|
-/
lemma prop_4_20_bad_event_probability (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    (h_i_add_steps : i + steps ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩)
    Pr_{ let r_challenges ←$ᵖ (Fin steps → L) }[
        foldingBadEvent 𝔽q β i steps h_i_add_steps f_i r_challenges ] ≤
    ((steps * domain_size) / Fintype.card L) := by
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
  let L_card := Fintype.card L

  -- Unfold the event definition to split into the two cases
  unfold foldingBadEvent
  by_cases h_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f_i)
  · -- CASE 1: Fiber-wise Close (The main focus of the provided text)
    simp only [h_close, ↓reduceDIte]
    let res := prop_4_20_case_1_fiberwise_close 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := steps) h_destIdx h_destIdx_le (f_i := f_i) (h_close := h_close)
    exact res
  · -- CASE 2: Fiber-wise Far
    -- The bad event is that the folded function becomes UDRClose.
    simp only [h_close, ↓reduceDIte]
    -- If fiberwise distance is "far" (≥ d_next / 2),
    -- then the probability of becoming "close" (< d_next / 2) is bounded.
    apply prop_4_20_case_2_fiberwise_far 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (steps := steps)
      h_destIdx h_destIdx_le (h_far := h_close)

open Classical in
omit [CharP L 2] [DecidableEq 𝔽q] hF₂ [NeZero ℓ] in
/-- Helper: If `f` and `g` agree on the fiber of `y`, their folds agree at `y`.
NOTE: this might not be needed -/
lemma fold_agreement_of_fiber_agreement (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i + steps ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L) (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩) :
    (∀ x, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps (by omega) x = y → f x = g x) →
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) f (r_challenges := r_challenges) y =
    (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) g (r_challenges := r_challenges) (y := y))) := by
  intro h_fiber_agree
  -- Expand to matrix form: fold(y) = Tensor(r) * M_y * fiber_vals
  rw [iterated_fold_eq_matrix_form 𝔽q β h_destIdx h_destIdx_le]
  rw [iterated_fold_eq_matrix_form 𝔽q β h_destIdx h_destIdx_le]
  -- ⊢ localized_fold_matrix_form 𝔽q β i steps h_i_add_steps f r y =
  -- localized_fold_matrix_form 𝔽q β i steps h_i_add_steps g r y
  unfold localized_fold_matrix_form single_point_localized_fold_matrix_form
  simp only
  congr 2
  let left := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) h_destIdx h_destIdx_le f y
  let right := fiberEvaluations 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) h_destIdx h_destIdx_le g y
  have h_fiber_eval_eq : left = right := by
    unfold left right fiberEvaluations
    ext idx
    let x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps) h_destIdx h_destIdx_le y idx
    have h_x_folds_to_y := generates_quotient_point_if_is_fiber_of_y 𝔽q β (i := i) (steps := steps)
          h_destIdx h_destIdx_le (x := x) (y := y) (hx_is_fiber := by use idx)
    exact h_fiber_agree x h_x_folds_to_y.symm
  unfold left right at h_fiber_eval_eq
  rw [h_fiber_eval_eq]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ [NeZero ℓ] in
/-- Helper: The disagreement set of the folded functions is a subset of the fiberwise disagreement set. -/
lemma disagreement_fold_subset_fiberwiseDisagreement (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i + steps ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_challenges : Fin steps → L) :
    let folded_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) f (r_challenges := r_challenges)
    let folded_g := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ steps
      (by simp only; apply Nat.lt_add_of_pos_right_of_le; omega) g (r_challenges := r_challenges)
    disagreementSet 𝔽q β ⟨i + steps, by omega⟩ folded_f folded_g ⊆
    fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g := by
  simp only
  intro y hy_mem
  simp only [disagreementSet, ne_eq, mem_filter, mem_univ, true_and] at hy_mem
  simp only [fiberwiseDisagreementSet, ne_eq, Subtype.exists, mem_filter, mem_univ, true_and]
  -- Contrapositive: If y is NOT in fiberwise disagreement, then f and g agree on fiber.
  -- Then folds must agree (lemma above). Then y is NOT in disagreement set.
  by_contra h_not_in_fiber_diff
  have h_agree_on_fiber : ∀ x, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps (by omega) x = y → f x = g x := by
    intro x hx
    by_contra h_neq
    exact h_not_in_fiber_diff ⟨x, (by simp only [SetLike.coe_mem]), (by simp only [Subtype.coe_eta]; constructor; exact hx; exact h_neq)⟩
  have h_fold_eq := fold_agreement_of_fiber_agreement 𝔽q β i steps h_i_add_steps f g (r_challenges := r_challenges) (y := y) h_agree_on_fiber
  exact hy_mem h_fold_eq

/-- **Lemma 4.24**
For `i*` where `f^(i)` is non-compliant, `f^(i+ϑ)` is UDR-close, and the bad event `E_{i*}`
doesn't occur, the folded function of `f^(i)` is not UDR-close to the UDR-decoded codeword
of `f^(i+ϑ)`. -/
lemma lemma_4_24_dist_folded_ge_of_last_noncompliant (i_star : Fin ℓ) (steps : ℕ) [NeZero steps]
    (h_bounds : i_star + steps ≤ ℓ)
    (f_star : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩)
    (f_next : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star + steps, by omega⟩)
    (r_challenges : Fin steps → L)
    -- 1. f_next is the actual folded function
    -- 2. i* is non-compliant
    (h_not_compliant : ¬ isCompliant 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i_star steps h_bounds
       f_star f_next (challenges := r_challenges))
    -- 3. No bad event occurred at i*
    (h_no_bad_event : ¬ foldingBadEvent 𝔽q β i_star steps h_bounds f_star r_challenges)
    -- 4. The next function `f_next` IS close enough to have a unique codeword `f_bar_next`
    (h_next_close : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star + steps, by omega⟩ f_next) :
      let f_i_star_folded := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       ⟨i_star, by omega⟩ steps (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i_star steps h_bounds) f_star r_challenges
    -- **CONCLUSION**: 2 * d(f_next, f_bar_next) ≥ d_{i* + steps}
    let f_bar_next := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star + steps, by omega⟩ (f := f_next) (h_within_radius := h_next_close)
    ¬ pair_UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star + steps, by omega⟩ f_i_star_folded f_bar_next := by

  -- Definitions for clarity
  let d_next := BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star + steps, by omega⟩
  let S_next := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i_star + steps, by omega⟩
  let C_cur := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩
  let C_next := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star + steps, by omega⟩
  let f_bar_next := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star + steps, by omega⟩
      (f := f_next) (h_within_radius := h_next_close)
  let f_i_star_folded := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
       ⟨i_star, by omega⟩ steps (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i_star steps h_bounds) f_star r_challenges

  have h_f_bar_next_mem_C_next : f_bar_next ∈ C_next := by -- due to definition
    unfold f_bar_next UDRCodeword
    apply UDRCodeword_mem_BBF_Code (i := ⟨i_star + steps, by omega⟩) (f := f_next) (h_within_radius := h_next_close)

  have h_d_next_ne_0 : d_next ≠ 0 := by
    unfold d_next
    simp only [BBF_CodeDistance_eq]
    omega
  let d_fw := fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i_star)
    steps (h_i_add_steps := h_bounds) (f := f_star)

  -- Split into Case 1 (Close) and Case 2 (Far)
  by_cases h_fw_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i_star) (steps := steps) (h_i_add_steps := h_bounds) (f := f_star)
  -- Case 1: Fiberwise Close (d < d_next / 2)
  · let h_fw_dist_lt := h_fw_close -- This gives 2 * fiber_dist < d_next
    -- Define f_bar_star (the unique decoded codeword for f_star) to be the **fiberwise**-close codeword to f_star
    obtain ⟨f_bar_star, ⟨h_f_bar_star_mem, h_f_bar_star_min_card, h_f_bar_star_eq_UDRCodeword⟩, h_unique⟩ := exists_unique_fiberwiseClosestCodeword_within_UDR 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i_star) (steps := steps) (h_i_add_steps := h_bounds) (f := f_star) (h_fw_close := h_fw_close)

    have h_fw_dist_f_g_eq : #(fiberwiseDisagreementSet 𝔽q β i_star steps h_bounds f_star f_bar_star) = d_fw := by
      unfold d_fw
      rw [h_f_bar_star_min_card]; rfl

    let folded_f_bar_star := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i_star, by omega⟩
       steps (by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i_star steps h_bounds) f_bar_star (r_challenges := r_challenges)

    have h_folded_f_bar_star_mem_C_next : folded_f_bar_star ∈ C_next := by
      unfold folded_f_bar_star
      apply iterated_fold_preserves_BBF_Code_membership 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i_star) (steps := steps) (h_i_add_steps := h_bounds) (f := ⟨f_bar_star, h_f_bar_star_mem⟩) (r_challenges := r_challenges)
    -- We prove two inequalities (1) and (2) as per the proof sketch.
    -- **Step (1): Distance between the two codewords in C_next**
    -- First, show that `folded_f_bar_star` ≠ `f_bar_next`.
    -- This follows because `f_star` is NON-COMPLIANT.
    have h_codewords_neq : f_bar_next ≠ folded_f_bar_star := by
      by_contra h_eq
      -- If they were equal, `isCompliant` would be true (satisfying all 3 conditions).
      apply h_not_compliant
      use h_fw_dist_lt -- Condition 1: f_star is close
      use h_next_close -- Condition 2: f_next is close
      -- Condition 3: folded decoding equals next decoding
      simp only
      rw [←h_f_bar_star_eq_UDRCodeword]
      -- ⊢ iterated_fold ⟨i*, ⋯⟩ steps ⋯ f_bar_star r_challenges = UDRCodeword 𝔽q β ⟨i* + steps, ⋯⟩ f_next h_next_close
      exact id (Eq.symm h_eq)

    -- Since they are distinct codewords, their distance is at least `d_next`.
    have h_ineq_1 : Δ₀(f_bar_next, folded_f_bar_star) ≥ d_next := by
      apply Code.pairDist_ge_code_mindist_of_ne (C := (C_next : Set _))
        (u := f_bar_next) (v := folded_f_bar_star)
      · exact h_f_bar_next_mem_C_next
      · exact h_folded_f_bar_star_mem_C_next
      · exact h_codewords_neq

    -- **Step (2): Distance between folded functions**
    -- We know |Δ_fiber(f*, f_bar*)| < d_next / 2 (from fiberwise close hypothesis).
    have h_fiber_dist_lt_half : 2 * (fiberwiseDisagreementSet 𝔽q β i_star steps h_bounds f_star f_bar_star).card < d_next := by
      rw [Nat.two_mul_lt_iff_le_half_of_sub_one (h_b_pos := by omega)]
      -- ⊢ #(fiberwiseDisagreementSet 𝔽q β i_star steps h_bounds f_star f_bar_star) ≤ (d_next - 1) / 2
      rw [h_fw_dist_f_g_eq]
      rw [←Nat.two_mul_lt_iff_le_half_of_sub_one (h_b_pos := by omega)]
      unfold d_fw
      unfold fiberwiseClose at h_fw_close
      norm_cast at h_fw_close

    -- Lemma 4.18 (Geometric): d(fold(f), fold(g)) ≤ |Δ_fiber(f, g)|
    have h_ineq_2 : 2 * Δ₀(f_i_star_folded, folded_f_bar_star) < d_next := by
      calc
        2 * Δ₀(iterated_fold 𝔽q β ⟨i_star, _⟩ steps _ f_star (r_challenges := r_challenges), folded_f_bar_star)
        _ ≤ 2 * (fiberwiseDisagreementSet 𝔽q β i_star steps h_bounds f_star f_bar_star).card := by
          -- Hamming distance is card(disagreementSet)
          -- disagreementSet ⊆ fiberwiseDisagreementSet (Lemma 4.18 Helper)
          apply Nat.mul_le_mul_left
          let res := disagreement_fold_subset_fiberwiseDisagreement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i_star) (steps := steps) (h_i_add_steps := h_bounds) (f := f_star) (g := f_bar_star) (r_challenges := r_challenges)
          simp only at res
          apply Finset.card_le_card
          exact res
        _ < d_next := h_fiber_dist_lt_half

    -- **Final Step: Reverse Triangle Inequality**
    -- d(A, C) ≥ d(B, C) - d(A, B)
    -- We want 2 * d(f_next, f_bar_next) ≥ d_next
    have h_triangle : Δ₀(f_bar_next, folded_f_bar_star) ≤ Δ₀(f_bar_next, f_i_star_folded) + Δ₀(f_i_star_folded, folded_f_bar_star) :=
      hammingDist_triangle f_bar_next f_i_star_folded folded_f_bar_star
    have h_final_bound : 2 * d_next ≤ 2 * Δ₀(f_bar_next, f_i_star_folded) + 2 * Δ₀(f_i_star_folded, folded_f_bar_star) := by
      have h_trans : d_next ≤ Δ₀(f_bar_next, folded_f_bar_star) := h_ineq_1
      have h_mul : 2 * d_next ≤ 2 * Δ₀(f_bar_next, folded_f_bar_star) := Nat.mul_le_mul_left 2 h_trans
      linarith [h_triangle, h_mul]
    -- We have 2*d_next ≤ 2*d(Target) + (something < d_next)
    -- This implies 2*d(Target) > d_next
    -- Or in integer arithmetic: 2*d(Target) ≥ d_next
    rw [hammingDist_comm] at h_final_bound -- align directions
    unfold pair_UDRClose
    simp only [not_lt, ge_iff_le]
    apply le_of_not_gt
    intro h_contra
    -- If 2 * d(target) < d_next:
    -- Sum < d_next + d_next = 2*d_next. Contradiction.
    linarith [h_ineq_2, h_final_bound, h_contra]
  -- **Case 2: Fiberwise Far (d ≥ d_next / 2)**
  · -- In this case, the definition of `foldingBadEvent` (Case 2 branch) simplifies.
    -- The bad event is defined as: UDRClose(f_next).
    unfold foldingBadEvent at h_no_bad_event
    simp only [h_fw_close, ↓reduceDIte] at h_no_bad_event
    -- h_no_bad_event : ¬ UDRClose ...
    -- This means f_next is NOT close to the code C_next.

    -- Definition of not UDRClose: 2 * dist(f_next, C_next) ≥ d_next
    unfold UDRClose at h_no_bad_event
    simp only [not_lt] at h_no_bad_event
    -- ↑(BBF_CodeDistance 𝔽q β ⟨↑i_star + steps, ⋯⟩)
    have h_no_bad_event_alt : (d_next : ℕ∞) ≤ 2 * Δ₀(f_i_star_folded, f_bar_next):= by
      calc
        d_next ≤ 2 * Δ₀(f_i_star_folded, (C_next : Set (S_next → L))) := by
          exact h_no_bad_event
        _ ≤ 2 * Δ₀(f_i_star_folded, f_bar_next) := by
          rw [ENat.mul_le_mul_left_iff]
          · simp [Code.distFromCode_le_dist_to_mem (C := (C_next : Set (S_next → L))) (u := f_i_star_folded) (v := f_bar_next) (hv := h_f_bar_next_mem_C_next)]
          · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
          · simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true]

    unfold pair_UDRClose
    simp only [not_lt, ge_iff_le]
    norm_cast at h_no_bad_event_alt

end
end Binius.BinaryBasefold
