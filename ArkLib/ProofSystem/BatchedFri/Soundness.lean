/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.Prelims
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.BatchedFri.Spec.General
import ArkLib.ProofSystem.Fri.Domain
import ArkLib.ProofSystem.Fri.Spec.General
import ArkLib.ProofSystem.Fri.Spec.SingleRound
import ArkLib.OracleReduction.Security.Basic
import ToMathlib.Control.OptionT
import ArkLib.ToMathlib.List.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors

namespace Fri
section Fri

open OracleComp OracleSpec ProtocolSpec CosetDomain
open NNReal Finset Function ProbabilityTheory

variable {𝔽 : Type} [NonBinaryField 𝔽] [Finite 𝔽] [DecidableEq 𝔽] [Nontrivial 𝔽]
variable (D : Subgroup 𝔽ˣ) (n : ℕ) [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (g : 𝔽ˣ) {k : ℕ}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)
variable {i : Fin (k + 1)}

noncomputable local instance : Fintype 𝔽 := Fintype.ofFinite _

instance {F : Type} [Field F] {a : F} [inst : NeZero a] : Invertible a where
  invOf := a⁻¹
  invOf_mul_self := by field_simp [inst.out]
  mul_invOf_self := by field_simp [inst.out]

#check Domain.domainEnum
#check Domain.rootsOfUnity

@[grind]
def cosetElems (s₀ : evalDomainSigma D g s i) : List (evalDomainSigma D g s i) :=
  if k_le_n : ∑ j', (s j').1 ≤ n
  then
    (Domain.rootsOfUnity D n (s i)).map fun r =>
      ⟨
        _,
        CosetDomain.mul_root_of_unity D (sum_finRangeTo_le_sub_of_le k_le_n) s₀.2 r.2
      ⟩
  else []

def cosetG (s₀ : evalDomainSigma D g s i) : Finset (evalDomainSigma D g s i) :=
  (cosetElems D n g s s₀).toFinset

def pows (z : 𝔽) (ℓ : ℕ) : Matrix Unit (Fin ℓ) 𝔽 :=
  Matrix.of <| fun _ j => z ^ j.val

def VDM (s₀ : evalDomainSigma D g s i) :
  Matrix (Fin (2 ^ (s i : ℕ))) (Fin (2 ^ (s i : ℕ))) 𝔽 :=
  if k_le_n : (∑ j', (s j').1) ≤ n
  then
    have : (cosetElems D n g s s₀).length = 2 ^ (s i : ℕ) := by
      unfold cosetElems Domain.rootsOfUnity
      simp [k_le_n, PNat.val]
    let v : Fin (2 ^ (s i).1) → 𝔽 :=
      fun x => ((cosetElems D n g s s₀).get ⟨x.1, by rw [this]; exact x.2⟩).1.1
    Matrix.vandermonde v
  else 1

noncomputable def fin_equiv_coset (s₀ : evalDomainSigma D g s i) :
    (Fin (2 ^ (s i).1)) ≃ { x // x ∈ cosetG D n g s s₀ } := by
  apply Equiv.ofBijective
  swap
  sorry
  sorry

def invertibleDomain (s₀ : evalDomainSigma D g s i) : Invertible (VDM D n g s s₀) := by
  haveI : NeZero (VDM D n g s s₀).det := by
    constructor
    unfold VDM
    split_ifs with cond
    · simp only [finRangeTo.eq_1, evalDomain.eq_1, Domain.evalDomain.eq_1, List.get_eq_getElem,
      Matrix.det_vandermonde]
      rw [Finset.prod_ne_zero_iff]
      intros i' _
      rw [Finset.prod_ne_zero_iff]
      intros j' h'
      have : i' ≠ j' := by
        rename_i a
        simp_all only [mem_univ, mem_Ioi, ne_eq]
        obtain ⟨val, property⟩ := s₀
        simp_all only [evalDomain, finRangeTo, Domain.evalDomain]
        apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [lt_self_iff_false]
      unfold cosetElems
      simp only [cond, ↓reduceDIte, Domain.evalDomain, finRangeTo,
        evalDomain, List.getElem_map, Units.val_mul]
      unfold Domain.rootsOfUnity
      simp only
        [
          Domain.evalDomain, List.getElem_map,
          List.getElem_range, Units.val_pow_eq_pow_val
        ]
      intros h
      apply this
      have :
          (DIsCyclicC.gen.1.1 ^ 2 ^ (n - (s i).1)) ^ j'.1 =
            (DIsCyclicC.gen.1.1 ^ 2 ^ (n - (s i).1)) ^ i'.1 := by
        have := (@sub_eq_zero 𝔽 _ _ _).mp h
        rw [mul_right_inj' (Units.ne_zero s₀.1)] at this
        exact this
      have pow_lift {a : 𝔽ˣ} {n : ℕ} : a.1 ^ n = (a ^ n).1 := rfl
      rw [pow_lift, pow_lift, pow_lift, Units.val_inj] at this
      have this := this.symm
      apply Fin.eq_of_val_eq
      have pow_eq {G : Type} [Group G] {a b : ℕ} {g : G} :
        a < orderOf g → b < orderOf g → g ^ a = g ^ b → a = b := by
        intros h₁ h₂ h₃
        rwa [pow_inj_mod, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at h₃
      refine pow_eq ?_ ?_ this
      · convert i'.2
        rw [orderOf_pow, orderOf_submonoid, DSmooth.1]
        have : 2 ^ n = 2 ^ ((n - (s i).1) + (s i).1) := by
          apply (Nat.pow_right_inj (by decide)).mpr
          refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
          transitivity
          swap
          · exact cond
          · have :=
              @Finset.single_le_sum (Fin (k + 1)) ℕ _ _ _
                (fun i => (s i).1) Finset.univ (by intros i _; simp)
                i (by simp)
            simp only at this
            exact this
        rw [this, pow_add, mul_comm, Nat.gcd_mul_left_left]
        simp
        rfl
      · convert j'.2
        rw [orderOf_pow, orderOf_submonoid, DSmooth.1]
        have : 2 ^ n = 2 ^ ((n - (s i).1) + (s i).1) := by
          apply (Nat.pow_right_inj (by decide)).mpr
          refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
          transitivity
          swap
          · exact cond
          · have :=
              @Finset.single_le_sum (Fin (k + 1)) ℕ _ _ _
                (fun i => (s i).1) Finset.univ (by intros i _; simp)
                i (by simp)
            simp only at this
            exact this
        rw [this, pow_add, mul_comm, Nat.gcd_mul_left_left]
        simp
        rfl
    · simp
  apply @Matrix.invertibleOfDetInvertible


noncomputable def VDMInv (s₀ : evalDomainSigma D g s i) :
  Matrix (Fin (2 ^ (s i).1)) (cosetG D n g s s₀) 𝔽 :=
  Matrix.reindex (Equiv.refl _) (fin_equiv_coset D n g s s₀)
  (invertibleDomain D n g s s₀).invOf

lemma g_elem_zpower_iff_exists_nat {G : Type} [Group G] [Finite G] {gen g : G} :
    g ∈ Subgroup.zpowers gen ↔ ∃ n : ℕ, g = gen ^ n ∧ n < orderOf gen := by
  have := isOfFinOrder_of_finite gen
  refine ⟨fun h ↦ ?p₁, ?p₂⟩
  · obtain ⟨k, h⟩ := Subgroup.mem_zpowers_iff.1 h
    let k' := k % orderOf gen
    have pow_pos : 0 ≤ k' := by apply Int.emod_nonneg; simp [*]
    obtain ⟨n, h'⟩ : ∃ n : ℕ, n = k' := by rcases k' with k' | k' <;> [(use k'; grind); aesop]
    use n
    have : gen ^ n = gen ^ k := by have := zpow_mod_orderOf gen k; grind [zpow_natCast]
    have : n < orderOf gen := by zify; rw [h']; apply Int.emod_lt; simp [isOfFinOrder_of_finite gen]
    grind
  · grind [Subgroup.npow_mem_zpowers]

example (g : 𝔽ˣ) : g⁻¹ * g = 1 := by
  exact inv_mul_cancel g


open Matrix in
noncomputable def f_succ'
  (f : evalDomainSigma D g s i → 𝔽) (z : 𝔽)
  (s₀' : evalDomainSigma D g s (i.1 + 1)) : 𝔽 :=
  have :
    ∃ s₀ : evalDomain D g (∑ j' ∈ finRangeTo (i.1), ↑(s j')),
      s₀.1 ^ (2 ^ (s i).1) = s₀'.1 := by
    have h := s₀'.2
    simp only [evalDomain] at h
    have :
      ((g ^ 2 ^ ∑ j' ∈ finRangeTo (↑i + 1), (s j').1))⁻¹ * s₀'.1 ∈
        Domain.evalDomain D (∑ j' ∈ finRangeTo (↑i + 1), ↑(s j'))
        := by
        aesop_reconcile
    simp only [Domain.evalDomain] at this
    rw [g_elem_zpower_iff_exists_nat] at this
    rcases this with ⟨m, this⟩
    have m_lt := this.2
    have := eq_mul_of_inv_mul_eq this.1
    iterate 2 rw [sum_finRangeTo_add_one, Nat.pow_add, pow_mul] at this
    rw [pow_right_comm _ _ m] at this
    use
      ⟨
        (g ^ 2 ^ ∑ j' ∈ finRangeTo ↑i, (s j').1) *
        ((DIsCyclicC.gen ^ 2 ^ ∑ j' ∈ finRangeTo ↑i, (s j').1) ^ m),
        by
          have := fun X₁ X₂ X₃ ↦ @mem_leftCoset_iff.{0} 𝔽ˣ _ X₁ X₂ X₃
          reconcile
          erw
            [
              evalDomain, this, ←mul_assoc, inv_mul_cancel,
              one_mul, Domain.evalDomain, SetLike.mem_coe
            ]
          exact Subgroup.npow_mem_zpowers _ _
      ⟩
    simp only [this, mul_pow]
    rfl
  let s₀ := Classical.choose this
  (pows z _ *ᵥ VDMInv D n g s s₀ *ᵥ Finset.restrict (cosetG D n g s s₀) f) ()

lemma claim_8_1
  {f : ReedSolomon.code (injectF (i := ∑ j' ∈ finRangeTo i, s j'))
                        (2 ^ (n - (∑ j' ∈ finRangeTo i, (s j' : ℕ))))}
  {z : 𝔽}
  :
  f_succ' D n g s f.val z ∈
    (ReedSolomon.code
      CosetDomain.injectF
      (2 ^ (n - (∑ j' ∈ finRangeTo (i.1 + 1), (s j' : ℕ))))
    ).carrier
  := by sorry

/-- Affine space: {g | ∃ x : Fin t.succ → 𝔽, x 0 = 1 ∧ g = ∑ i, x i • f i  }
-/
def Fₛ {ι : Type} [Fintype ι] {t : ℕ} (f : Fin t.succ → (ι → 𝔽)) : AffineSubspace 𝔽 (ι → 𝔽) :=
  f 0 +ᵥ affineSpan 𝔽 (Finset.univ.image (f ∘ Fin.succ))

noncomputable def correlated_agreement_density {ι : Type} [Fintype ι]
  (Fₛ : AffineSubspace 𝔽 (ι → 𝔽)) (V : Submodule 𝔽 (ι → 𝔽)) : ℝ :=
  let Fc := Fₛ.carrier.toFinset
  let Vc := V.carrier.toFinset
  (Fc ∩ Vc).card / Fc.card

open Polynomial

noncomputable def oracleImpl (l : ℕ) (z : Fin (k + 1) → 𝔽) (f : (CosetDomain.evalDomain D g 0) → 𝔽) :
  QueryImpl
    ([]ₒ ++ₒ ([Spec.FinalOracleStatement D g s]ₒ ++ₒ [(Spec.QueryRound.pSpec D g l).Message]ₒ))
    (OracleComp [(Spec.QueryRound.pSpec D g l).Message]ₒ) where
      impl :=
        fun q ↦
          match q with
          | query (.inl i) _ => PEmpty.elim i
          | query (.inr (.inl i)) dom =>
            let f0 := Lagrange.interpolate Finset.univ (fun v => v.1.1) f
            let chals : List (Fin (k + 1) × 𝔽) :=
              ((List.finRange (k + 1)).map (fun i => (i, z i))).take i.1
            let fi : 𝔽[X] := List.foldl (fun f (i, α) => Polynomial.foldNth (s i) f α) f0 chals
            if h : i.1 = k + 1
            then pure <| by
              simp only
                [
                  OracleSpec.range, OracleSpec.append,
                  OracleInterface.toOracleSpec, Spec.FinalOracleStatement
                ]
              unfold OracleInterface.Response Spec.instOracleInterfaceFinalOracleStatement
              simp [h]
              exact fi
            else pure <| by
              simp only
                [
                  OracleSpec.range, OracleSpec.append,
                  OracleInterface.toOracleSpec, Spec.FinalOracleStatement
                ]
              unfold OracleInterface.Response Spec.instOracleInterfaceFinalOracleStatement
              simp [h]
              simp only
                [
                  OracleSpec.domain, OracleSpec.append,
                  OracleInterface.toOracleSpec, Spec.FinalOracleStatement
                ] at dom
              unfold OracleInterface.Query Spec.instOracleInterfaceFinalOracleStatement at dom
              simp only [h, ↓reduceDIte] at dom
              exact fi.eval dom.1.1
          | query (.inr (.inr i)) t => OracleComp.lift (query i t)

instance {g : 𝔽ˣ} {l : ℕ} : [(Spec.QueryRound.pSpec D g l).Message]ₒ.FiniteRange where
  range_inhabited' := by
    intros i
    unfold Spec.QueryRound.pSpec MessageIdx at i
    have : i.1 = 0 := by omega
    have h := this ▸ i.2
    simp at h
  range_fintype' := by
    intros i
    unfold Spec.QueryRound.pSpec MessageIdx at i
    have : i.1 = 0 := by omega
    have h := this ▸ i.2
    simp at h

-- #check  BatchedFri.Spec.BatchingRound.instOracleInterfaceMessageBatchSpec
-- #check Spec.QueryRound.instOracleInterfaceMessagePSpec
-- omit [BatchedFri.Spec.BatchingRound.instOracleInterfaceMessageBatchSpec 1] in
open ENNReal in
lemma lemma_8_2
  {t : ℕ}
  {α : ℝ}
  (f : Fin t.succ → (CosetDomain.evalDomain D g 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code ⟨fun x => x.1.1, fun a b h ↦ by aesop⟩ (2 ^ n))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  :
    let ρ_sqrt :=
      ReedSolomonCode.sqrtRate
        (2 ^ n)
        (Embedding.trans (CosetDomain.domainEnum (n := n) D g 0) (CosetDomain.domainEmb D g))
    let α0 : ℝ≥0∞ := ENNReal.ofReal (max α (ρ_sqrt * (1 + 1 / 2 * m)))
    let εC : ℝ≥0∞ := ENNReal.ofReal <|
      (m + (1 : ℚ)/2)^7 * (2^n)^2
        / (2 * ρ_sqrt ^ 3) * (Fintype.card 𝔽)
      + (∑ i, (s i).1) * (2 * m + 1) * (2 ^ n + 1) / (Fintype.card 𝔽 * ρ_sqrt)
    let εQ  (x : Fin t → 𝔽)
            (z : Fin (k + 1) → 𝔽) :=
      Pr_{let samp ←$ᵖ (CosetDomain.evalDomain D g 0)}[
        [
          fun _ => True |
          (
            (do
              simulateQ
                (oracleImpl D g s 1 z (fun v ↦ f 0 v + ∑ i, x i * f i.succ v))
                (
                  (
                    Fri.Spec.QueryRound.queryVerifier D g
                      (n := n) (k := k) (s := s) (l := 1)
                        (by
                          apply Spec.round_bound (d := d)
                          transitivity
                          · exact domain_size_cond
                          · apply pow_le_pow (by decide) (by decide)
                            simp
                        )
                  ).verify
                  z
                  (fun i =>
                    by
                      simpa only
                        [
                          Spec.QueryRound.pSpec, Challenge,
                          show i.1 = 0 by omega, Fin.isValue,
                          Fin.vcons_zero
                        ] using fun _ => samp
                  )
                )
            )
          )
        ] = 1
      ]
    Pr_{let x ←$ᵖ (Fin t → 𝔽); let z ←$ᵖ (Fin (k + 1) → 𝔽)}[ εQ x z ≤ α0 ] ≤ εC
  := by sorry

#check (BatchedFri.Spec.BatchingRound.batchOracleReduction D g s 1 0).verifier

@[reducible]
def MaliciousWitness (F : Type) [Semiring F] (m : ℕ) :=
  Fin (m + 1) → (CosetDomain.evalDomain D g 0 → 𝔽)

#check OracleReduction.run
#check BatchedFri.Spec.BatchingRound.batchSpec
#check ProtocolSpec.Challenge
#check OracleReduction.verifier
#check BatchedFri.Spec.batchedFRIreduction

#check [_]ₒ

set_option diagnostics true
instance {t l : ℕ} : ([]ₒ ++ₒ
      [(BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t ++ₚ
            (Spec.pSpecFold D g k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
              Spec.QueryRound.pSpec D g l)).Challenge]ₒ).FiniteRange := sorry

#check ProtocolSpec.instOracleInterfaceMessageAppend

#check BatchedFri.Spec.BatchingRound.batchSpec
variable {l : ℕ}
#check (Spec.pSpecFold D g k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ Spec.QueryRound.pSpec D g l)
#check OracleVerifier

open ENNReal in
lemma lemma_8_3
  {t l : ℕ}
  (f : Fin t.succ → (CosetDomain.evalDomain D g 0 → 𝔽))
  {m r : ℕ}
  (m_ge_3 : m ≥ 3)
  :
    let ρ_sqrt :=
      ReedSolomonCode.sqrtRate
        (2 ^ n)
        (Embedding.trans (CosetDomain.domainEnum (n := n) D g 0) (CosetDomain.domainEmb D g))
    let α : ℝ≥0∞ := ENNReal.ofReal (ρ_sqrt * (1 + 1 / 2 * m))
    letI bl :=
      @ProtocolSpec.instOracleInterfaceMessageAppend 1 ((Fin.vsum fun (x : Fin k) ↦ 2) + 2 + 1)
        (BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) (Spec.pSpecFold D g k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ Spec.QueryRound.pSpec D g l)
        inferInstance inferInstance
    -- have :
    let verif : OracleVerifier []ₒ Unit (BatchedFri.Spec.OracleStatement D g t) (Spec.FinalStatement 𝔽 k) (Spec.FinalOracleStatement D g s) (BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t ++ₚ
      (Spec.pSpecFold D g k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ Spec.QueryRound.pSpec D g l)) := by
      have blo := BatchedFri.Spec.batchedFRIreduction (n := n) D g k s (2 ^ (n - ∑ j, (s j).1)) sorry l t
      have : bl = fun i ↦ ProtocolSpec.instOracleInterfaceMessageAppend i := by
        dsimp [bl]
        funext
        rfl
      rw [←this] at blo
      exact blo.verifier
    let bla :=
      ∃ prov,
      [
          fun _ => True |
            OracleReduction.run () f ()
              ⟨
                prov,
                verif
              ⟩
      ] > 0
    True := sorry

-- failed to synthesize
--   (i :
--       (BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t ++ₚ
--           (Spec.pSpecFold D g k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ Spec.QueryRound.pSpec D g l)).MessageIdx) →
--     OracleInterface
--       ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t ++ₚ
--             (Spec.pSpecFold D g k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ Spec.QueryRound.pSpec D g l)).Message
--         i)

end Fri
end Fri
