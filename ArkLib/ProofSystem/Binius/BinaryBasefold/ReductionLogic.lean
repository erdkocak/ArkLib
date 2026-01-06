/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.Execution
import ArkLib.OracleReduction.Completeness

set_option maxHeartbeats 400000  -- Increase if needed
set_option profiler true
-- set_option profiler.threshold 50  -- Show anything taking over 10ms
namespace Binius.BinaryBasefold.CoreInteraction
/-!
## Binary Basefold single steps
- **Fold step** :
  P sends V the polynomial `h_i(X) := Σ_{w ∈ B_{ℓ-i-1}} h(r'_0, ..., r'_{i-1}, X, w_0, ...
  w_{ℓ-i-2})`.
  V requires `s_i ?= h_i(0) + h_i(1)`. V samples `r'_i ← L`, sets `s_{i+1} := h_i(r'_i)`,
  and sends P `r'_i`.
- **Relay step** : transform relOut of fold step in case of non-commitment round to match
  roundRelation
- **Commit step** :
    P defines `f^(i+1): S^(i+1) → L` as the function `fold(f^(i), r'_i)` of Definition 4.6.
    if `i+1 < ℓ` and `ϑ | i+1` then
    P submits (submit, ℓ+R-i-1, f^(i+1)) to the oracle `F_Vec^L`
- **Final sum-check step** :
  - P sends V the final constant `c := f^(ℓ)(0, ..., 0)`
  - V verifies : `s_ℓ = eqTilde(r, r') * c`
  => `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})`
-/
noncomputable section
open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
open Binius.BinaryBasefold
open scoped NNReal

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SelectableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

section GenericLogic

def hEq {ιₒᵢ ιₒₒ : Type} {OracleIn : ιₒᵢ → Type}
  {OracleOut : ιₒₒ → Type} {n : ℕ} {pSpec : ProtocolSpec n}
  (embed : ιₒₒ ↪ ιₒᵢ ⊕ pSpec.MessageIdx) :=
  ∀ i, OracleOut i =
    match embed i with
    | Sum.inl j => OracleIn j
    | Sum.inr j => pSpec.Message j

/-- The Pure Logic of an interactive reduction step.
Parametrized by a 'Challenges' type that aggregates all verifier randomness. -/
structure ReductionLogicStep
    (StmtIn WitIn : Type)
    {ιₒᵢ ιₒₒ : Type}
    (OracleIn : ιₒᵢ → Type) (OracleOut : ιₒₒ → Type)
    (StmtOut WitOut : Type)
    {n : ℕ} (pSpec : ProtocolSpec n) where

  -- 1. The Specification (Relations) - now with indexed oracles
  completeness_relIn    : (StmtIn × (∀ i, OracleIn i)) × WitIn → Prop
  completeness_relOut   : (StmtOut × (∀ i, OracleOut i)) × WitOut → Prop

  -- 2. The Verifier (Pure Logic)
  verifierCheck : StmtIn → FullTranscript pSpec → Prop
  verifierOut   : StmtIn → FullTranscript pSpec → StmtOut

  -- 2b. Oracle Embedding (like OracleVerifier)
  embed : ιₒₒ ↪ ιₒᵢ ⊕ pSpec.MessageIdx
  hEq : hEq (OracleIn := OracleIn) (OracleOut := OracleOut) (ιₒᵢ := ιₒᵢ) (ιₒₒ := ιₒₒ)
    (pSpec := pSpec) (embed := embed)

  -- 3. The Honest Prover (Pure Logic)
  honestTranscript : StmtIn → WitIn → (∀ i, OracleIn i) → pSpec.Challenges → FullTranscript pSpec

  -- 4. The Prover's Output State
  proverOut : StmtIn → WitIn → (∀ i, OracleIn i) → FullTranscript pSpec →
    ((StmtOut × (∀ i, OracleOut i)) × WitOut)

/-- Strong Completeness:
  "For ANY set of challenges, the honest transcript passes the check
   and leads to a valid next state." -/
@[reducible]
def ReductionLogicStep.IsStronglyComplete
    {StmtIn WitIn : Type}
    {ιₒᵢ ιₒₒ : Type} {OracleIn : ιₒᵢ → Type} {OracleOut : ιₒₒ → Type}
    {StmtOut WitOut : Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    (step : ReductionLogicStep StmtIn WitIn OracleIn OracleOut StmtOut WitOut pSpec) : Prop :=
  ∀ (stmtIn : StmtIn) (witIn : WitIn) (oStmtIn : ∀ i, OracleIn i) (challenges : pSpec.Challenges),

    -- Assumption: The input relation holds (valid start state)
    (h_relIn : step.completeness_relIn ((stmtIn, oStmtIn), witIn)) →

    -- 1. Generate the Honest Transcript (Deterministic given challenges)
    let transcript := step.honestTranscript stmtIn witIn oStmtIn challenges

    -- 2. The Verifier MUST accept this transcript
    step.verifierCheck stmtIn transcript ∧

    -- 3. The output MUST be valid and consistent
    let verifierStmtOut := step.verifierOut stmtIn transcript

    -- Compute verifier oracle output via embedding (like OracleVerifier.toVerifier)
    let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
      oStmtIn transcript
      -- fun i => match h : step.embed i with
      -- | Sum.inl j => by simpa only [step.hEq, h] using (oStmtIn j)
      -- | Sum.inr j => by simpa only [step.hEq, h] using (transcript.messages j)

    let ((proverStmtOut, proverOStmtOut), proverWitOut) :=
      step.proverOut stmtIn witIn oStmtIn transcript

    -- Conclusion A: The Prover's output satisfies the next relation (Soundness/Completeness)
    step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) ∧

    -- Conclusion B: The Prover and Verifier agree on the next statement
    proverStmtOut = verifierStmtOut ∧

    -- Conclusion C: The Prover and Verifier agree on the oracle statements
    proverOStmtOut = verifierOStmtOut

end GenericLogic

section SingleIteratedSteps
variable {Context : Type} {mp : SumcheckMultiplierParam L ℓ Context} -- Sumcheck context
section FoldStep

/-- The Logic Instance for the i-th round of Binary Folding. -/
def foldStepLogic (i : Fin ℓ) :
    ReductionLogicStep
      -- In/Out Types
      (Statement (L := L) Context i.castSucc)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (Statement (L := L) Context i.succ)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      -- Protocol Spec
      (pSpecFold (L := L))
      where

  -- 1. Relations
  completeness_relIn := fun ((s, o), w) =>
    ((s, o), w) ∈ roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i.castSucc (mp := mp) (includeBadEvents := false)
  completeness_relOut := fun ((s, o), w) =>
    ((s, o), w) ∈ foldStepRelOut 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i (mp := mp) (includeBadEvents := false)

  -- 2. Verifier Logic (Using extracted kernels)
  verifierCheck := fun s t =>
    foldVerifierCheck i s (𝓑 := 𝓑) (t.messages ⟨0, rfl⟩)

  verifierOut := fun s t =>
    foldVerifierStmtOut i s (t.messages ⟨0, rfl⟩) (t.challenges ⟨1, rfl⟩)

  -- 2b. Oracle Embedding (must match foldOracleVerifier)
  embed := ⟨fun j => by
    if hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc then
      exact Sum.inl ⟨j.val, by omega⟩
    else omega -- never happens
  , by
    intro a b h_ab_eq
    simp only [MessageIdx, Fin.is_lt, ↓reduceDIte, Fin.eta, Sum.inl.injEq] at h_ab_eq
    exact h_ab_eq
  ⟩
  hEq := fun oracleIdx => by
    simp only [MessageIdx, Fin.is_lt, ↓reduceDIte, Fin.eta, Function.Embedding.coeFn_mk]

  -- 3. Honest Prover Logic (Constructing the transcript)
  --    "Given input and the future challenge, what would the transcript look like?"
  honestTranscript := fun _stmtIn witIn _oStmtIn chal =>
    let msg : ↥L⦃≤ 2⦄[X] := foldProverComputeMsg (L := L) 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i witIn
    FullTranscript.mk2 msg (chal ⟨1, rfl⟩)

  -- 4. Prover Output (State Update)
  proverOut := fun s w o t =>
    let h_i : (pSpecFold (L := L)).«Type» 0 := t ⟨0, by omega⟩
    let r_i' : (pSpecFold (L := L)).«Type» 1 := t ⟨1, by omega⟩
    getFoldProverFinalOutput 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
      (s, o, w, h_i, r_i')

variable {R : Type} [CommSemiring R] [DecidableEq R] [SelectableType R]
  {n : ℕ} {deg : ℕ} {m : ℕ} {D : Fin m ↪ R}
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}

omit [SelectableType L] in
/-- The Main Lemma: Binary Folding satisfies Strong Completeness.

This proves that for any valid input satisfying `roundRelation`, the honest prover-verifier
interaction correctly computes the sumcheck polynomial and updates the witness through folding.

**Proof Structure:**
- Verifier check: Uses `projectToNextSumcheckPoly_sum_eq`.
- Output relation: Uses `badEventExistsProp_succ_preserved` for bad events, and preservation lemmas
  (e.g., `witnessStructuralInvariant_succ_preserved`) otherwise.
- Agreement: Prover and verifier agree on output statements and oracles. -/
lemma foldStep_is_logic_complete (i : Fin ℓ) :
    (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
      (mp := mp) i).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := (foldStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i)
  let transcript := step.honestTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  -- Extract properties from h_relIn (roundRelation)
  simp only [foldStepLogic, roundRelation, roundRelationProp, Set.mem_setOf_eq] at h_relIn

  -- Extract the disjunction from masterKStateProp
  simp only [masterKStateProp] at h_relIn

  -- We'll need sumcheck consistency for Fact 1, so extract it from either branch
  have h_sumcheck_cons : sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H
    := h_relIn.1

  let h_VCheck_passed : step.verifierCheck stmtIn transcript := by
    -- Fact 1: Verifier check passes (sumcheck condition)
    simp only [step, foldStepLogic, foldVerifierCheck, foldProverComputeMsg]
    rw [h_sumcheck_cons]
    apply getSumcheckRoundPoly_sum_eq

  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    -- Fact 3: Prover and verifier statements agree
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    simp only [step, foldStepLogic]; simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, Fin.val_succ]

  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.2
      = OracleVerifier.mkVerifierOStmtOut step.embed step.hEq oStmtIn transcript
    simp only [step, foldStepLogic]
    -- Fact 4: Prover and verifier oracle statements agree
    funext j
    have hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc := j.isLt
    simp only [OracleVerifier.mkVerifierOStmtOut, Function.Embedding.coeFn_mk, Fin.eta]
    split
    · rename_i j' heq
      -- heq : (if hj : ↑j < ... then Sum.inl j else ...) = Sum.inl j'
      -- Since hj holds, we have Sum.inl j = Sum.inl j', so j = j'
      simp only [hj, ↓reduceDIte] at heq
      cases heq
      rfl
    · rename_i heq
      -- This case is impossible: the if-then-else evaluates to Sum.inl j when hj holds
      -- So we have Sum.inl j = Sum.inr j✝, which is a contradiction
      simp only [hj, ↓reduceDIte] at heq
      -- heq : Sum.inl j = Sum.inr j✝ is a contradiction
      cases heq

  -- Key fact: Oracle statements are unchanged in the fold step
  -- (all oracle indices map via Sum.inl in the embedding)
  have h_verifierOStmtOut_eq : verifierOStmtOut = oStmtIn := by
    rw [← hOStmtOut_eq]
    simp only [proverOStmtOut, proverOutput, step, foldStepLogic]

  let hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    -- Fact 2: Output relation holds (foldStepRelOut)
    simp only [step, foldStepLogic, foldStepRelOut, foldStepRelOutProp, Set.mem_setOf_eq]
    simp only [masterKStateProp]
    let r_i' := challenges ⟨1, rfl⟩
    simp only [Fin.val_succ, Bool.false_eq_true, ↓reduceIte]
    constructor
    · -- Part 2.1: sumcheck consistency
      unfold sumcheckConsistencyProp
      dsimp only [verifierStmtOut, proverWitOut, proverOutput]
      simp only [step, foldStepLogic, foldVerifierStmtOut, getFoldProverFinalOutput, transcript]
      apply projectToNextSumcheckPoly_sum_eq
    · -- Part 2.2: master state (bad event or consistency)
      simp only [Fin.coe_castSucc, Bool.false_eq_true, ↓reduceIte] at h_relIn
      have h_oracleWitConsistency_In := h_relIn.2
      rw [h_verifierOStmtOut_eq];
      dsimp only [oracleWitnessConsistency] at h_oracleWitConsistency_In ⊢
      -- Extract the three components from the input
      obtain ⟨h_wit_struct_In, h_first_oracle_In, h_oracle_folding_In⟩ :=
        h_oracleWitConsistency_In
      -- Now prove each component for the output
      refine ⟨?_, ?_, ?_⟩
      · -- Component 1: witnessStructuralInvariant
        unfold witnessStructuralInvariant
        obtain ⟨h_H_In, h_f_In⟩ := h_wit_struct_In
        dsimp only [Fin.val_succ, proverWitOut, proverOutput, step,
          foldStepLogic, verifierStmtOut]
        constructor
        · conv_lhs =>
            rw [h_H_In]
            rw [←projectToMidSumcheckPoly_succ]
          rfl
        · conv_lhs =>
            rw [h_f_In]
            rw [←getMidCodewords_succ]
          rfl
      · -- Component 2: firstOracleWitnessConsistencyProp
        exact h_first_oracle_In
      · -- Component 3: oracleFoldingConsistencyProp
        have h_oracleIdx_eq : (OracleFrontierIndex.mkFromStmtIdx i.castSucc).val
          = (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i).val := by rfl
        have h_challenges_eq : Fin.init verifierStmtOut.challenges = stmtIn.challenges := by
          dsimp only [foldStepLogic, Fin.isValue, MessageIdx, Fin.is_lt, Fin.eta,
            Lean.Elab.WF.paramLet, Matrix.cons_val_zero, Fin.zero_eta, Matrix.cons_val_one,
            Fin.mk_one, Fin.val_succ, verifierStmtOut, step]
          simp only [Fin.isValue, Fin.init_snoc]
        rw! (castMode := .all) [h_oracleIdx_eq] at h_oracle_folding_In
        simp at h_oracle_folding_In ⊢
        rw [h_challenges_eq]
        exact h_oracle_folding_In

  -- Prove the four required facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

end FoldStep

section CommitStep

def commitStepLogic_embedFn (i : Fin ℓ) :
  (Fin (toOutCodewordsCount ℓ ϑ i.succ)) → Fin (toOutCodewordsCount ℓ ϑ i.castSucc) ⊕ (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).MessageIdx :=
  fun j => by
  if hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc then
    exact Sum.inl ⟨j.val, hj⟩
  else
    exact Sum.inr ⟨⟨0, Nat.zero_lt_one⟩, rfl⟩

def commitStepLogic_embed_inj (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    Function.Injective (commitStepLogic_embedFn  𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i) := by
  intro a b h_ab_eq
  simp only [MessageIdx, commitStepLogic_embedFn, Fin.isValue] at h_ab_eq
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

/- the CommitStep is a 1-message oracle reduction to place the conditional oracle message -/
def commitStepLogic_embed (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
Fin (toOutCodewordsCount ℓ ϑ i.succ) ↪ Fin (toOutCodewordsCount ℓ ϑ i.castSucc) ⊕ (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).MessageIdx := ⟨
  commitStepLogic_embedFn  𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i
  , commitStepLogic_embed_inj 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i hCR
  ⟩

-- ⊢ ∀ (i_1 : Fin (toOutCodewordsCount ℓ ϑ i.succ)),
--   OracleStatement 𝔽q β ϑ i.succ i_1 =
--     match (commitStepLogic_embed 𝔽q β i hCR) i_1 with
--     match (commitStepLogic_embed 𝔽q β ϑ i hCR) i_1 with
--     | Sum.inl j => OracleStatement 𝔽q β ϑ i.castSucc j
--     | Sum.inr j => (pSpecCommit 𝔽q β i).Message j

def commitStepHEq (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
  hEq (OracleIn := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc)
    (OracleOut := OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.succ)
    (ιₒᵢ := Fin (toOutCodewordsCount ℓ ϑ i.castSucc)) (ιₒₒ := Fin (toOutCodewordsCount ℓ ϑ i.succ))
    (pSpec := pSpecCommit 𝔽q β i) (embed := commitStepLogic_embed 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (ϑ := ϑ) i hCR)
  := fun oracleIdx => by
    unfold OracleStatement pSpecCommit commitStepLogic_embed commitStepLogic_embedFn
    simp only [MessageIdx, Fin.isValue, Function.Embedding.coeFn_mk, Message,
      Matrix.cons_val_fin_one]
    by_cases hlt : oracleIdx.val < toOutCodewordsCount ℓ ϑ i.castSucc
    · simp only [hlt, ↓reduceDIte]
    · simp only [hlt, ↓reduceDIte, Fin.isValue]
      have hOracleIdx_lt : oracleIdx.val < toOutCodewordsCount ℓ ϑ i.succ := by omega
      simp only [toOutCodewordsCount_succ_eq ℓ ϑ i, hCR, ↓reduceIte] at hOracleIdx_lt
      have hOracleIdx : oracleIdx = toOutCodewordsCount ℓ ϑ i.castSucc := by omega
      simp_rw [hOracleIdx]
      have h := toOutCodewordsCount_mul_ϑ_eq_i_succ ℓ ϑ (i := i) (hCR := hCR)
      unfold OracleFunction
      congr 1; congr 1
      funext x
      congr 1; congr 1
      simp only [Fin.mk.injEq]; rw [h]

/-- The Logic Instance for the commit step.
This is a trivial 1-message protocol where the prover just sends an oracle and the verifier accepts it. -/
def commitStepLogic (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    ReductionLogicStep
      (Statement (L := L) Context i.succ)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.castSucc)
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (Statement (L := L) Context i.succ)
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i.succ)
      (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) where

  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ foldStepRelOut (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (includeBadEvents := false) i

  completeness_relOut := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ roundRelation (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (includeBadEvents := false) i.succ

  -- No verification needed - just accept
  verifierCheck := fun _ _ => True

  -- Statement doesn't change
  verifierOut := fun stmt _ => stmt

  -- Oracle embedding: new oracle index maps to the message
  embed := commitStepLogic_embed 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR

  hEq := (commitStepHEq 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR)

  -- No challenges in 1-message protocol, so transcript is just the message
  honestTranscript := fun _stmt wit _oStmt _challenges =>
    fun ⟨0, _⟩ => wit.f

  -- Prover output: statement unchanged, oracle extended with new function
  proverOut := fun stmt wit oStmtIn transcript =>
    let oStmtOut :=
    snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) oStmtIn (newOracleFn := wit.f)
      -- OracleVerifier.mkVerifierOStmtOut
      -- (embed := (commitStepLogic_embed 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR))
      -- (hEq := (commitStepHEq 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i hCR))
      -- oStmtIn transcript
    ((stmt, oStmtOut), wit)

omit [CharP L 2] [SelectableType L] in
set_option profiler.threshold 1 in
/-- Helper lemma: snoc_oracle matches mkVerifierOStmtOut for commit steps.

This proves that when we add a new oracle via `snoc_oracle`, the result matches what the verifier
computes using `OracleVerifier.mkVerifierOStmtOut` with the commit step's embedding.

The key insight:
- For indices `j < toOutCodewordsCount ℓ ϑ i.castSucc`: embed maps to `Sum.inl j` (old oracle)
- For index `j = toOutCodewordsCount ℓ ϑ i.castSucc`: embed maps to `Sum.inr 0` (new oracle from message)
-/
lemma snoc_oracle_eq_mkVerifierOStmtOut_commitStep
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracle : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := ⟨i.val + 1, by omega⟩))
    (transcript : FullTranscript (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
    (h_transcript_eq : transcript.messages ⟨0, rfl⟩ = newOracle) :
    snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (destIdx := ⟨i.val + 1, by omega⟩) (h_destIdx := by rfl) oStmtIn newOracle =
    OracleVerifier.mkVerifierOStmtOut (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed
      (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (𝓑 := 𝓑) i hCR).hEq oStmtIn transcript := by
  funext j
  dsimp only [snoc_oracle]
  simp only [hCR, ↓reduceDIte]
  by_cases hj : j.val < toOutCodewordsCount ℓ ϑ i.castSucc
  · -- Old oracle case: embed j = Sum.inl
    have h_embed : (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed j = Sum.inl ⟨j.val, hj⟩ := by
      simp only [commitStepLogic, commitStepLogic_embed, Function.Embedding.coeFn_mk,
        commitStepLogic_embedFn, hj, dif_pos]
    rw [OracleVerifier.mkVerifierOStmtOut_inl _ _ _ _ _ _ h_embed]
    simp only [hj, dif_pos]
    rfl
  · -- New oracle case: embed j = Sum.inr 0
    have h_embed : (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) i hCR).embed j = Sum.inr ⟨0, rfl⟩ := by
      simp only [commitStepLogic, commitStepLogic_embed, Function.Embedding.coeFn_mk,
        commitStepLogic_embedFn, hj, dif_neg, not_false_eq_true]
      rfl
    rw [OracleVerifier.mkVerifierOStmtOut_inr _ _ _ _ _ _ h_embed]
    simp only [hj, dif_neg, not_false_eq_true]
    rw [← h_transcript_eq]

omit [CharP L 2] [SelectableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] in
/-- The first oracle is preserved when snocing a new oracle.

Since `getFirstOracle` extracts index 0, and `snoc_oracle` at index 0 always falls into
the "old oracle" branch (0 < toOutCodewordsCount), the first oracle is unchanged.
-/
lemma getFirstOracle_snoc_oracle
    (i : Fin ℓ) {destIdx : Fin r} (h_destIdx : destIdx = i.val + 1)
    (oStmtIn : ∀ j : Fin (toOutCodewordsCount ℓ ϑ i.castSucc),
      OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ i.castSucc j)
    (newOracleFn : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := destIdx)) :
    getFirstOracle 𝔽q β (snoc_oracle 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      h_destIdx oStmtIn newOracleFn) = getFirstOracle 𝔽q β oStmtIn := by
  unfold getFirstOracle snoc_oracle
  have h_lt : 0 < toOutCodewordsCount ℓ ϑ i.castSucc := by
    have h := (instNeZeroNatToOutCodewordsCount ℓ ϑ i.castSucc).out
    omega
  simp only [Fin.mk_zero', h_lt, ↓reduceDIte]
  rfl

/-- Oracle folding consistency is preserved when adding a new oracle in a commit step.

This lemma shows that if `oStmtIn` satisfies `oracleFoldingConsistencyProp` at round `i.castSucc`,
then `oStmtOut` (constructed via `mkVerifierOStmtOut` with commit step's embed/hEq) satisfies it at `i.succ`.

**Key insight**: In a commit step:
- The oracle frontier index values are equal: `(mkFromStmtIdxCastSuccOfSucc i).val = (mkFromStmtIdx i.succ).val`
- The challenges don't change (commit step has no verifier challenges)
- Therefore oracle folding consistency trivially carries over
-/
lemma oracleFoldingConsistency_commitStep
    (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i)
    (stmtIn : Statement (L := L) Context i.succ)
    (witIn : Witness 𝔽q β i.succ)
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ i.castSucc j)
    (challenges : (pSpecCommit 𝔽q β i).Challenges)
    (h_oracle_folding_In : oracleFoldingConsistencyProp 𝔽q β
      (i := (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i).val)
      (challenges := Fin.take (m := (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i).val)
        (v := stmtIn.challenges) (h := by simp only [Fin.val_fin_le, OracleFrontierIndex.val_le_i]))
      (oStmt := oStmtIn) (includeFinalFiberwiseClose := true)) :
    let step := (commitStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑) (mp := mp) i (hCR := hCR))
    let transcript := step.honestTranscript stmtIn witIn oStmtIn challenges
    let verifierStmtOut := step.verifierOut stmtIn transcript
    let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
      oStmtIn transcript
    oracleFoldingConsistencyProp 𝔽q β (ϑ := ϑ)
      (i := (OracleFrontierIndex.mkFromStmtIdx i.succ).val)
      (challenges := Fin.take (m := (OracleFrontierIndex.mkFromStmtIdx i.succ).val)
        (v := verifierStmtOut.challenges) (h := by simp only [Fin.val_fin_le, OracleFrontierIndex.val_le_i]))
      (oStmt := verifierOStmtOut) (includeFinalFiberwiseClose := true) := by
  -- The frontier indices are equal (definitionally)
  have h_frontier_eq : (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i).val
      = (OracleFrontierIndex.mkFromStmtIdx i.succ).val := sorry
  -- -- Therefore the challenges are also equal
  -- have h_challenges_eq : Fin.take (m := (OracleFrontierIndex.mkFromStmtIdx i.succ).val)
  --     (v := stmt.challenges) (h := by simp only [Fin.val_fin_le, OracleFrontierIndex.val_le_i])
  --   = Fin.take (m := (OracleFrontierIndex.mkFromStmtIdxCastSuccOfSucc i).val)
  --     (v := stmt.challenges) (h := by simp only [Fin.val_fin_le, OracleFrontierIndex.val_le_i]) := by
  --   simp only [h_frontier_eq]
  -- -- Rewrite and apply
  -- rw [h_frontier_eq, h_challenges_eq]
  -- exact h_oracle_folding_In
  sorry

/-- Commit step logic is strongly complete.
The key insight is that the commit step just extends the oracle without changing the statement,
and the verifier always accepts (no verification check). -/
lemma commitStep_is_logic_complete (i : Fin ℓ) (hCR : isCommitmentRound ℓ ϑ i) :
    (commitStepLogic (mp := mp) 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) i (hCR := hCR)).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := (commitStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑) (mp := mp) i (hCR := hCR))
  let transcript := step.honestTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2

  -- Extract properties from h_relIn (roundRelation)
  dsimp only [commitStepLogic, roundRelation, foldStepRelOut, foldStepRelOutProp,
    roundRelationProp, Set.mem_setOf_eq] at h_relIn
  dsimp only [masterKStateProp, Fin.val_succ, Bool.false_eq_true, ↓reduceIte] at h_relIn

  -- We'll need sumcheck consistency for Fact 1, so extract it from either branch
  have h_sumcheck_cons : sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H
    := h_relIn.1
  let h_VCheck_passed : step.verifierCheck stmtIn transcript := by
    dsimp only [commitStepLogic, Prod.mk.eta, step]

  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    dsimp only [step, commitStepLogic]
  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by
    -- clear_value h_VCheck_passed
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.2
      = OracleVerifier.mkVerifierOStmtOut step.embed step.hEq oStmtIn transcript
    conv_lhs => dsimp only [step, commitStepLogic]
    dsimp only [transcript, step]
    rw [snoc_oracle_eq_mkVerifierOStmtOut_commitStep 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)]; rfl

  have h_first_oracle_eq : (getFirstOracle 𝔽q β verifierOStmtOut)
    = (getFirstOracle 𝔽q β oStmtIn) := by
    rw [← hOStmtOut_eq]
    dsimp only [proverOStmtOut, proverOutput, step, commitStepLogic]
    exact getFirstOracle_snoc_oracle 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (by rfl) oStmtIn _

  let hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    -- clear_value h_VCheck_passed
    -- Fact 2: Output relation holds (foldStepRelOut)
    dsimp only [step, commitStepLogic, foldStepRelOut, foldStepRelOutProp,
      roundRelation, roundRelationProp, Set.mem_setOf_eq]
    dsimp only [masterKStateProp]
    -- let r_i' := challenges ⟨1, rfl⟩
    simp only [Fin.val_succ, Bool.false_eq_true, ↓reduceIte]
    constructor
    · -- Part 2.1: sumcheck consistency
      exact h_sumcheck_cons
    · -- Part 2.2: master state (bad event or consistency)
      have h_oracleWitConsistency_In := h_relIn.2
      -- rw [h_verifierOStmtOut_eq];
      dsimp only [oracleWitnessConsistency] at h_oracleWitConsistency_In ⊢
      -- Extract the three components from the input
      obtain ⟨h_wit_struct_In, h_first_oracle_In, h_oracle_folding_In⟩ :=
        h_oracleWitConsistency_In
      -- Now prove each component for the output
      refine ⟨?_, ?_, ?_⟩
      · -- Component 1: witnessStructuralInvariant
        exact h_wit_struct_In
      · -- Component 2: firstOracleWitnessConsistencyProp
        rw [h_first_oracle_eq]
        exact h_first_oracle_In
      · -- Component 3: oracleFoldingConsistencyProp
        exact oracleFoldingConsistency_commitStep 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) (witIn := witIn) (stmtIn := stmtIn) (hCR := hCR)
          (h_oracle_folding_In := h_oracle_folding_In) (challenges := challenges)

  -- Prove the four required facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

end CommitStep

section FinalSumcheckStep
/-!
## Final Sumcheck Step

This section implements the final sumcheck step that sends the constant `c := f^(ℓ)(0, ..., 0)`
from the prover to the verifier. This step completes the sumcheck verification by ensuring
the final constant is consistent with the folding chain.

The step consists of :
- P → V : constant `c := f^(ℓ)(0, ..., 0)`
- V verifies : `s_ℓ = eqTilde(r, r') * c`
=> `c` should be equal to `t(r'_0, ..., r'_{ℓ-1})` and `f^(ℓ)(0, ..., 0)`

**Key Mathematical Insight** : At round ℓ, we have :
- `P^(ℓ)(X) = Σ_{w ∈ B_0} H_ℓ(w) · X_w^(ℓ)(X) = H_ℓ(0) · X_0^(ℓ)(X) = H_ℓ(0)`
- Since `H_ℓ(X)` is constant (zero-variate): `H_ℓ(X) = t(r'_0, ..., r'_{ℓ-1})`
- Therefore : `P^(ℓ)(X) = t(r'_0, ..., r'_{ℓ-1})` (constant polynomial)
- And `s_ℓ = ∑_{w ∈ B_0} t(r'_0, ..., r'_{ℓ-1}) = t(r'_0, ..., r'_{ℓ-1})`
-/

/-- Oracle interface instance for the final sumcheck step message -/
instance : ∀ j, OracleInterface ((pSpecFinalSumcheckStep (L := L)).Message j) := fun j =>
  match j with
  | ⟨0, _⟩ => OracleInterface.instDefault

/-- The Logic Instance for the final sumcheck step.
This is a 1-message protocol where the prover sends the final constant c. -/
def finalSumcheckStepLogic :
    ReductionLogicStep
      -- In/Out Types
      (Statement (L := L) (SumcheckBaseContext L ℓ) (Fin.last ℓ))
      (Witness (L := L) 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (OracleStatement 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ))
      (FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
      (Unit)
      -- Protocol Spec
      (pSpecFinalSumcheckStep (L := L))
      where

  completeness_relIn := fun ((stmt, oStmt), wit) =>
    ((stmt, oStmt), wit) ∈ roundRelation 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑) (mp := BBF_SumcheckMultiplierParam) (Fin.last ℓ) (includeBadEvents := false)

  completeness_relOut := fun ((stmtOut, oStmtOut), witOut) =>
    ((stmtOut, oStmtOut), witOut) ∈ finalSumcheckRelOut 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (includeBadEvents := false)

  verifierCheck := fun stmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    let eq_tilde_eval := eqTilde (r := stmtIn.ctx.t_eval_point) (r' := stmtIn.challenges)
    stmtIn.sumcheck_target = eq_tilde_eval * c

  verifierOut := fun stmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }

  honestTranscript := fun _stmtIn witIn _oStmtIn _chal =>
    -- The honest prover sends c = f^(ℓ)(0, ..., 0)
    let c : L := witIn.f ⟨0, by simp only [zero_mem]⟩
    FullTranscript.mk1 c

  proverOut := fun stmtIn witIn oStmtIn transcript =>
    let c : L := transcript.messages ⟨0, rfl⟩
    let stmtOut : FinalSumcheckStatementOut (L := L) (ℓ := ℓ) := {
      ctx := stmtIn.ctx,
      sumcheck_target := stmtIn.sumcheck_target,
      challenges := stmtIn.challenges,
      final_constant := c
    }
    ((stmtOut, oStmtIn), ())

  embed := ⟨fun j => by
    have h_lt : j.val < toOutCodewordsCount ℓ ϑ (Fin.last ℓ) := j.isLt
    exact Sum.inl ⟨j.val, by omega⟩
  , by
    intro a b h_ab_eq
    simp only [MessageIdx, Fin.eta, Sum.inl.injEq] at h_ab_eq
    exact h_ab_eq
  ⟩
  hEq := fun oracleIdx => by simp only [Fin.eta]

/-- When folding from a UDR codeword at the last oracle level to level `ℓ` (final sumcheck),
the iterated fold of the UDR codeword equals the UDR codeword of the constant function.

This lemma is used in the final sumcheck step to show that the folding chain correctly
terminates at the constant function. It takes the full context from the final sumcheck step
(statement, witness, oracle statement, transcript) to match the proof pattern. -/
lemma iterated_fold_to_const_UDRCodeword
    (stmtIn : Statement (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witIn : Witness 𝔽q β (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ (Fin.last ℓ) j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_oracleWitConsistency_In : oracleWitnessConsistency 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (Context := SumcheckBaseContext L ℓ) (mp := BBF_SumcheckMultiplierParam)
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (stmt := stmtIn) (wit := witIn) (oStmt := oStmtIn)) :
    let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    let transcript := step.honestTranscript stmtIn witIn oStmtIn challenges
    let verifierStmtOut := step.verifierOut stmtIn transcript
    let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq oStmtIn transcript
    let last_oracle_fn_pos_idx := getLastOraclePositionIndex (ℓ := ℓ) (ϑ := ϑ) (Fin.last ℓ)
    let k := getLastOracleDomainIndex (ℓ := ℓ) (ϑ := ϑ) (Fin.last ℓ)

    let h_le := getLastOracleDomainIndex_add_ϑ_le ℓ ϑ (i := Fin.last ℓ)
    let left := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := ⟨getLastOracleDomainIndex (ℓ := ℓ) (ϑ := ϑ) (Fin.last ℓ), by omega⟩)
      (steps := ϑ) (destIdx := ⟨getLastOracleDomainIndex (ℓ := ℓ) (ϑ := ϑ) (Fin.last ℓ) + ϑ, by omega⟩) (by rfl) (by simp only [getLastOracleDomainIndex_add_ϑ_le]; omega)
      -- (h_i_add_steps := by
        -- simp only [oracle_index_add_steps_le_ℓ, Nat.lt_add_of_pos_right_of_le])
      (f := UDRCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨getLastOracleDomainIndex (ℓ := ℓ) (ϑ := ϑ) (Fin.last ℓ), by
        rw [getLastOracleDomainIndex_last]; omega⟩) (h_i := by
          have h_le := oracle_index_add_steps_le_ℓ ℓ ϑ (i := Fin.last ℓ)
            (j := getLastOraclePositionIndex (ℓ := ℓ) (ϑ := ϑ) (Fin.last ℓ))
          simp only; omega
        )
        (f := verifierOStmtOut last_oracle_fn_pos_idx) (h_within_radius := by
          dsimp only [oracleWitnessConsistency] at h_oracleWitConsistency_In
          let res := h_oracleWitConsistency_In.2.2
          dsimp only [oracleFoldingConsistencyProp] at res
          let res := res.2
          simp only [↓reduceIte, Fin.val_last, OracleFrontierIndex.val_mkFromStmtIdx]
          at res
          -- dsimp only [getLastOracleDomainIndex, oraclePositionToDomainIndex] at res
          apply UDRClose_of_fiberwiseClose 𝔽q β (i := ⟨getLastOracleDomainIndex ℓ ϑ (Fin.last ℓ), by
            rw [getLastOracleDomainIndex_last]; omega⟩) (steps := ϑ) (destIdx := ⟨getLastOracleDomainIndex (ℓ := ℓ) (ϑ := ϑ) (Fin.last ℓ) + ϑ, by omega⟩) (by rfl) (by simp only [getLastOracleDomainIndex_add_ϑ_le]; omega)
            (f := verifierOStmtOut last_oracle_fn_pos_idx) res
        ))
      (r_challenges := fun cId => verifierStmtOut.challenges ⟨k + cId.val, by
        simp only [Fin.val_last]; omega⟩)

    ∀ y, left y = transcript.messages ⟨0, rfl⟩ := by
  sorry

omit [CharP L 2] [SelectableType L] in
/-- The honest transcript in the final sumcheck step sends c = witIn.f(0). -/
lemma honestTranscript_constant_eq_f_zero
    (stmtIn : Statement (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witIn : Witness 𝔽q β (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ (Fin.last ℓ) j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges) :
    let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    let transcript := step.honestTranscript stmtIn witIn oStmtIn challenges
    transcript.messages ⟨0, rfl⟩ = witIn.f ⟨0, by simp only [zero_mem]⟩ := by
  simp only [finalSumcheckStepLogic]

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

set_option maxHeartbeats 100000
/-- The verifier check passes in the final sumcheck step.

**Proof structure:**
1. From `sumcheckConsistencyProp`:
   - `stmtIn.sumcheck_target = ∑ x ∈ 𝓑^ᶠ(0), witIn.H.val.eval x`
   - Since `𝓑^ᶠ(0) = {∅}`, this simplifies to `witIn.H.val.eval (fun _ => 0)`

2. From `witnessStructuralInvariant`:
   - `witIn.H = projectToMidSumcheckPoly ...`
   - Using `projectToMidSumcheckPoly_at_last`:
   - `witIn.H.val.eval (fun _ => 0) = eqTilde(...) * witIn.f ⟨0, ...⟩`

3. Combining these gives the verifier check equation. -/
lemma finalSumcheckStep_verifierCheck_passed
    (stmtIn : Statement (SumcheckBaseContext L ℓ) (Fin.last ℓ))
    (witIn : Witness 𝔽q β (Fin.last ℓ))
    (oStmtIn : ∀ j, OracleStatement 𝔽q β ϑ (Fin.last ℓ) j)
    (challenges : (pSpecFinalSumcheckStep (L := L)).Challenges)
    (h_sumcheck_cons : sumcheckConsistencyProp (𝓑 := 𝓑) stmtIn.sumcheck_target witIn.H)
    (h_oracleWitConsistency_In : oracleWitnessConsistency 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (Context := SumcheckBaseContext L ℓ) (mp := BBF_SumcheckMultiplierParam)
      (stmtIdx := Fin.last ℓ) (oracleIdx := OracleFrontierIndex.mkFromStmtIdx (Fin.last ℓ))
      (stmt := stmtIn) (wit := witIn) (oStmt := oStmtIn)) :
    let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
    let transcript := step.honestTranscript stmtIn witIn oStmtIn challenges
    step.verifierCheck stmtIn transcript := by
  let step := finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (𝓑 := 𝓑)
  let transcript := step.honestTranscript stmtIn witIn oStmtIn challenges

  -- Simplify the verifier check to the equality we need to prove
  change (finalSumcheckStepLogic 𝔽q β).verifierCheck stmtIn transcript
  simp only [finalSumcheckStepLogic]
  dsimp only [sumcheckConsistencyProp] at h_sumcheck_cons

  -- Simplify the sum to a single evaluation since 𝓑^ᶠ(0) = {∅}
  rw [Finset.sum_eq_single (a := fun _ => 0) (h₀ := fun b _ hb_ne => by
    have : b = fun x ↦ 0 := by
      funext i;
      rw [Fin.val_last] at i
      simp only [tsub_self] at i; exact i.elim0
    contradiction
    ) (h₁ := fun h_not_mem => by
      exfalso; apply h_not_mem
      simp only [Fintype.mem_piFinset]; intro x
      rw [Fin.val_last] at x
      simp only [tsub_self] at x; exact x.elim0
    )] at h_sumcheck_cons

  have h_wit_structural_invariant := h_oracleWitConsistency_In.1

  have h_f_eq_getMidCodewords_t : witIn.f = getMidCodewords 𝔽q β witIn.t stmtIn.challenges :=
    h_wit_structural_invariant.2

  have h_witIn_f_0_eq_c : witIn.f ⟨0, by simp only [zero_mem]⟩ = transcript.messages ⟨0, rfl⟩ := by
    rfl
  let h_c_eq : (transcript.messages ⟨0, rfl⟩) = witIn.t.val.eval stmtIn.challenges := by
    change witIn.f ⟨0, by simp only [zero_mem]⟩ = witIn.t.val.eval stmtIn.challenges
    -- Since `f (f_ℓ)` is `getMidCodewords` of `t`, `f = fold(f₀, r') where f₀ = fun x => t.eval x`
    dsimp only [getMidCodewords, Fin.coe_ofNat_eq_mod] at h_f_eq_getMidCodewords_t
    rw [congr_fun h_f_eq_getMidCodewords_t ⟨0, by simp only [zero_mem]⟩]
    --   ⊢ iterated_fold 𝔽q β 0 ℓ ⋯
    --   (fun x ↦ Polynomial.eval ↑x ↑(polynomialFromNovelCoeffsF₂ 𝔽q β ℓ ⋯ fun ω ↦ (MvPolynomial.eval ↑↑ω) ↑witIn.t))
    --   stmtIn.challenges ⟨↑⟨0, ⋯⟩, ⋯⟩ =
    -- (MvPolynomial.eval stmtIn.challenges) ↑witIn.t
    -- have h_eq : @Fin.mk r (0 % ℓ) (isLt := by exact Nat.pos_of_ne_zero (by omega)) = 0 := by
      -- simp only [Nat.zero_mod, Fin.mk_zero']
    let coeffs := fun (ω : Fin (2 ^ (ℓ - 0))) => witIn.t.val.eval (bitsOfIndex ω)
    let res := iterated_fold_advances_evaluation_poly 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := 0) (steps := Fin.last ℓ) (destIdx := ⟨↑(Fin.last ℓ), by omega⟩) (by simp only [Fin.val_last, Fin.coe_ofNat_eq_mod,
        Nat.zero_mod, zero_add]) (by simp only; omega)
      (coeffs := coeffs) (r_challenges := stmtIn.challenges)
    unfold polyToOracleFunc at res
    simp only at res
    rw [intermediate_poly_P_base 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (h_ℓ := by omega) (coeffs := coeffs)] at res
    dsimp only [polynomialFromNovelCoeffsF₂]
    -- dsimp only [coeffs]
    change iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) 0 ↑(Fin.last ℓ)
      (destIdx := ⟨↑(Fin.last ℓ), by omega⟩) (by simp only [Fin.val_last, Fin.coe_ofNat_eq_mod,
        Nat.zero_mod, zero_add]) (by simp only; omega)
        (fun x ↦
          Polynomial.eval (↑x) (polynomialFromNovelCoeffs 𝔽q β ℓ (h_ℓ := by omega) coeffs))
        stmtIn.challenges ⟨0, by simp only [Fin.val_last, zero_mem]⟩ =
      (MvPolynomial.eval stmtIn.challenges) (witIn.t.val)
    rw [res]
    --   (intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate ⟨0 % ℓ + ℓ, ⋯⟩ fun j ↦
    --     ∑ x, multilinearWeight stmtIn.challenges x * coeffs ⟨↑j * 2 ^ ℓ + ↑x, ⋯⟩) =
    -- (MvPolynomial.eval stmtIn.challenges) ↑witIn.t
    dsimp only [intermediateEvaluationPoly]
    -- have h_empty_univ : Fin (ℓ - (Fin.last ℓ)) = Fin 0 := by
      -- simp only [Fin.val_last, tsub_self]

    haveI : IsEmpty (Fin (ℓ - (Fin.last ℓ).val)) := by
      simp only [Fin.val_last, Nat.sub_self]
      infer_instance
    conv_lhs => -- Eliminate the intermediateNovelBasisX terms
      dsimp only [intermediateNovelBasisX]
      simp only [Finset.univ_eq_empty, Finset.prod_empty] -- eliminate the finsum over (Fin 0)
      simp only [map_mul, mul_one]
      rw [←map_sum] -- bring the `C` out of the sum
    have h_Fin_eq : Fin (2 ^ (ℓ - ↑(Fin.last ℓ))) = Fin 1 := by
      simp only [Fin.val_last, tsub_self, pow_zero]
    haveI : Unique (Fin (2 ^ (ℓ - (Fin.last ℓ).val))) := by
      simp only [Fin.val_last, Nat.sub_self, pow_zero]
      exact Fin.instUnique
    have h_default : (@default (Fin (2 ^ (ℓ - ↑(Fin.last ℓ)))) Unique.instInhabited).val = 0 := by
      have hlt := (@default (Fin (2 ^ (ℓ - ↑(Fin.last ℓ)))) Unique.instInhabited).isLt
      simp only [Fin.val_last, Nat.sub_self, pow_zero] at hlt
      exact Nat.lt_one_iff.mp hlt
    simp only [Fintype.sum_unique, Fin.val_zero, h_default]
    simp only [Fin.val_last, Nat.sub_zero, zero_mul, zero_add, Fin.eta, map_sum, map_mul]
    dsimp only [Nat.sub_zero, Fin.isValue, coeffs]
    simp only [←map_mul, ←map_sum]
    letI : NeZero (Fin.last ℓ).val := {
      out := by
        have h_ℓ_pos : ℓ > 0 := by exact Nat.pos_of_neZero ℓ
        rw [Fin.val_last]; omega
    }
    let res := multilinear_eval_eq_sum_bool_hypercube (challenges := stmtIn.challenges)
      (t := witIn.t)
    simp only [Fin.val_last] at res
    rw [res, Polynomial.eval_C];

  -- Apply `projectToMidSumcheckPoly_at_last` to connect H.eval with eqTilde * f(0)
  have h_H_eval_at_zero_eq_mul : witIn.H.val.eval (fun _ => (0 : L)) =
      eqTilde stmtIn.ctx.t_eval_point stmtIn.challenges *
      (witIn.f ⟨0, by simp only [zero_mem]⟩) := by
    rw [h_witIn_f_0_eq_c]
    have h_H_eq_projectToMidSumcheckPoly := h_wit_structural_invariant.1
    rw [←Subtype.val_inj] at h_H_eq_projectToMidSumcheckPoly
    rw [projectToMidSumcheckPoly_eq_prod] at h_H_eq_projectToMidSumcheckPoly
    rw [h_H_eq_projectToMidSumcheckPoly, map_mul]
    let h_eval1 := fixFirstVariablesOfMQP_full_eval_eq_eval (ℓ := ℓ)
        (poly := (BBF_SumcheckMultiplierParam.multpoly stmtIn.ctx).val)
        (challenges := stmtIn.challenges)
        (hp := (BBF_SumcheckMultiplierParam.multpoly stmtIn.ctx).property)
        (x := fun (_ : Fin (ℓ - (Fin.last ℓ).val)) => (0 : L))
    let h_eval2 := fixFirstVariablesOfMQP_full_eval_eq_eval (ℓ := ℓ)
        (poly := witIn.t.val)
        (challenges := stmtIn.challenges)
        (hp := witIn.t.property)
        (x := fun (_ : Fin (ℓ - (Fin.last ℓ).val)) => (0 : L))
    simp only [Fin.val_last, eval_zero']
    simp only [Fin.val_last, eval_zero'] at h_eval1 h_eval2
    rw [h_eval1, h_eval2]
    conv_rhs => rw [h_c_eq]
    dsimp only [BBF_SumcheckMultiplierParam, BBF_eq_multiplier, Fin.val_last, eqTilde]

  -- Combine to finish the proof
  change stmtIn.sumcheck_target = eqTilde stmtIn.ctx.t_eval_point stmtIn.challenges *
    witIn.f ⟨0, by simp only [Fin.val_last, zero_mem]⟩
  rw [←h_H_eval_at_zero_eq_mul]
  exact h_sumcheck_cons

/-- Final sumcheck step logic is strongly complete.
**Key Proof Obligations:**
1. **Verifier Check**: Show that `stmtIn.sumcheck_target = eq_tilde_eval * c` where `c = wit.f ⟨0, ...⟩`
   - This should follow from `h_relIn` (roundRelation) which includes `oracleWitnessConsistency`
   - The `oracleWitnessConsistency` includes:
     * `witnessStructuralInvariant`: `wit.H = projectToMidSumcheckPoly ...` and `wit.f = getMidCodewords ...`
     * `sumcheckConsistencyProp`: `stmt.sumcheck_target = ∑ x ∈ (univ.map 𝓑) ^ᶠ (ℓ - ℓ), wit.H.val.eval x`
       For `i = Fin.last ℓ`, we have `ℓ - ℓ = 0`, so this is a sum over 0 variables
   - Need to connect these properties to show the verifier check passes

2. **Relation Out**: Show that the output satisfies `finalSumcheckRelOut`
   - This involves showing `finalFoldingStateProp` holds for the output
-/
lemma finalSumcheckStep_is_logic_complete :
    (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (𝓑 := 𝓑)).IsStronglyComplete := by
  intro stmtIn witIn oStmtIn challenges h_relIn
  let step := (finalSumcheckStepLogic 𝔽q β (ϑ := ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (𝓑 := 𝓑))
  let transcript := step.honestTranscript stmtIn witIn oStmtIn challenges
  let verifierStmtOut := step.verifierOut stmtIn transcript
  let verifierOStmtOut := OracleVerifier.mkVerifierOStmtOut step.embed step.hEq
    oStmtIn transcript
  let proverOutput := step.proverOut stmtIn witIn oStmtIn transcript
  let proverStmtOut := proverOutput.1.1
  let proverOStmtOut := proverOutput.1.2
  let proverWitOut := proverOutput.2
  let c := transcript.messages ⟨0, rfl⟩

  -- Extract properties from h_relIn BEFORE any simp changes its structure
  simp only [finalSumcheckStepLogic, roundRelation, roundRelationProp, Set.mem_setOf_eq] at h_relIn
  obtain ⟨h_sumcheck_cons, h_oracleWitConsistency_In⟩ := h_relIn
  let h_VCheck_passed := finalSumcheckStep_verifierCheck_passed 𝔽q β (𝓑 := 𝓑) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (witIn := witIn)
    (oStmtIn := oStmtIn) (challenges := challenges)
    (h_sumcheck_cons := h_sumcheck_cons)
    (h_oracleWitConsistency_In := h_oracleWitConsistency_In)

  have hStmtOut_eq : proverStmtOut = verifierStmtOut := by
    change (step.proverOut stmtIn witIn oStmtIn transcript).1.1 = step.verifierOut stmtIn transcript
    simp only [step, finalSumcheckStepLogic]

  have hOStmtOut_eq : proverOStmtOut = verifierOStmtOut := by rfl -- not new oracles added

  have h_first_oracle_eq : (getFirstOracle 𝔽q β verifierOStmtOut)
    = (getFirstOracle 𝔽q β oStmtIn) := by
    rw [← hOStmtOut_eq]
    simp only [proverOStmtOut, proverOutput, step, finalSumcheckStepLogic, getFirstOracle]

  let hRelOut : step.completeness_relOut ((verifierStmtOut, verifierOStmtOut), proverWitOut) := by
    -- clear_value h_VCheck_passed
    -- Fact 2: Output relation holds (foldStepRelOut)
    simp only [finalSumcheckStepLogic, roundRelation, roundRelationProp, Fin.val_last, Prod.mk.eta,
      Set.mem_setOf_eq, finalSumcheckRelOut, finalSumcheckRelOutProp, finalFoldingStateProp,
      Bool.false_eq_true, ↓reduceIte, Fin.isValue, Fin.eta, step]
    -- let r_i' := challenges ⟨1, rfl⟩
    -- rw [h_verifierOStmtOut_eq];
    dsimp only [oracleWitnessConsistency, Fin.val_last, OracleFrontierIndex.mkFromStmtIdx,
      oracleFoldingConsistencyProp, Fin.eta, ↓dreduceIte,
    Bool.false_eq_true] at h_oracleWitConsistency_In ⊢
    -- Extract the three components from the input
    let ⟨h_wit_struct_In, h_first_oracle_In, h_oracle_folding_In⟩ :=
      h_oracleWitConsistency_In
    -- Now prove each component for the output
    refine ⟨?_, ?_⟩
    · -- Component 1: oracleFoldingConsistencyProp
      rw [and_true]
      exact h_oracle_folding_In.1
    · -- Component 2: finalOracleFoldingConsistency
      dsimp only [isCompliant, Lean.Elab.WF.paramLet]
      refine ⟨?_, ?_, ?_⟩
      · -- Component 2.1: fiberwise-closeness for the last EXPLICIT oracle
        -- `This is guaranteed by finalFoldingStateProp in relIn`
        let res := h_oracle_folding_In.2
        exact res
      · apply constFunc_UDRClose
      · -- Component 2.3: decoded codewords consistency
        rw [UDRCodeword_constFunc_eq_self]
        funext y
        let res := iterated_fold_to_const_UDRCodeword 𝔽q β (𝓑 := 𝓑) (ϑ := ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (stmtIn := stmtIn) (witIn := witIn)
          (oStmtIn := oStmtIn) (challenges := challenges)
          (h_oracleWitConsistency_In := h_oracleWitConsistency_In)
        simp only at res; rw [res]; rfl

  -- Prove the four required facts
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_VCheck_passed
  · exact hRelOut
  · exact hStmtOut_eq
  · exact hOStmtOut_eq

end FinalSumcheckStep
end SingleIteratedSteps
end
end Binius.BinaryBasefold.CoreInteraction
