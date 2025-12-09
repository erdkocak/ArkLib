/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.Prelims
import ArkLib.Data.CodingTheory.ProximityGap
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

def cosetEnum (s₀ : evalDomainSigma D g s i) (k_le_n : ∑ j', (s j').1 ≤ n)
      (j : Fin (2 ^ (s i).1)) : { x // x ∈ evalDomainSigma D g s ↑i } :=
  let r : Domain.evalDomain D (n - ↑(s i)) :=
        Domain.domainEnum D
          ⟨n - (s i).1, show n - (s i).1 < n + 1 by omega⟩
          ⟨j.1,
            by
              simp only
              rw [Nat.sub_sub_eq_min]
              apply lt_of_lt_of_le j.2
              rw [Nat.pow_le_pow_iff_right Nat.le.refl, Nat.le_min]
              apply And.intro
              · refine le_trans ?_ k_le_n
                apply Finset.single_le_sum (f := fun i ↦ (s i).1) <;> simp
              · exact Nat.le_refl _
          ⟩
  ⟨
    _,
    CosetDomain.mul_root_of_unity D (sum_finRangeTo_le_sub_of_le k_le_n) s₀.2 r.2
  ⟩

def cosetG (s₀ : evalDomainSigma D g s i) : Finset (evalDomainSigma D g s i) :=
  if k_le_n : ∑ j', (s j').1 ≤ n
  then
    (Finset.univ).image (cosetEnum D n g s s₀ k_le_n)
  else ∅

def pows (z : 𝔽) (ℓ : ℕ) : Matrix Unit (Fin ℓ) 𝔽 :=
  Matrix.of <| fun _ j => z ^ j.val

def VDM (s₀ : evalDomainSigma D g s i) :
  Matrix (Fin (2 ^ (s i : ℕ))) (Fin (2 ^ (s i : ℕ))) 𝔽 :=
  if k_le_n : (∑ j', (s j').1) ≤ n
  then Matrix.vandermonde (fun j => (cosetEnum D n g s s₀ k_le_n j).1.1)
  else 1

def cosetEnum' (s₀ : evalDomainSigma D g s i) (k_le_n : ∑ j', (s j').1 ≤ n)
      (j : Fin (2 ^ (s i).1)) : cosetG D n g s s₀ :=
  ⟨
    cosetEnum D n g s s₀ k_le_n j,
    by simp [cosetG, k_le_n]
  ⟩

noncomputable def fin_equiv_coset (s₀ : evalDomainSigma D g s i) (k_le_n : ∑ j', (s j').1 ≤ n) :
    (Fin (2 ^ (s i).1)) ≃ { x // x ∈ cosetG D n g s s₀ } := by
  apply Equiv.ofBijective (cosetEnum' D n g s s₀ k_le_n)
  unfold cosetEnum' cosetEnum
  unfold Function.Bijective
  apply And.intro
  · intros a b
    aesop
  · rintro ⟨⟨y, h'⟩, h⟩
    simp
    unfold evalDomainSigma at h'
    -- unfold evalDomain Domain.evalDomain at h'
    -- have : ∃ a : Fin (2 ^ (s i).1),
    --    y =
    --     (g ^ 2 ^ ∑ j' ∈ finRangeTo ↑i, (s j').1) *
    --       (DIsCyclicC.gen.1 ^ 2 ^ ∑ j' ∈ finRangeTo ↑i, (s j').1) ^ a.1 := by sorry
    -- rcases this with ⟨a, h⟩
    -- use a




    -- simp only [evalDomain.eq_1, finRangeTo.eq_1, Domain.evalDomain.eq_1]
    sorry

def invertibleDomain (s₀ : evalDomainSigma D g s i) : Invertible (VDM D n g s s₀) := by
  haveI : NeZero (VDM D n g s s₀).det := by
    constructor
    unfold VDM
    split_ifs with cond
    · simp only [Matrix.det_vandermonde]
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
      intros contra
      apply this
      rw [sub_eq_zero, cosetEnum, cosetEnum] at contra
      norm_cast at contra
      rw [mul_left_cancel_iff] at contra
      norm_cast at contra
      rw [Function.Embedding.apply_eq_iff_eq, Fin.mk.injEq] at contra
      exact Fin.eq_of_val_eq (id (Eq.symm contra))
    · simp
  apply @Matrix.invertibleOfDetInvertible

noncomputable def VDMInv (s₀ : evalDomainSigma D g s i) (k_le_n : ∑ j', (s j').1 ≤ n) :
  Matrix (Fin (2 ^ (s i).1)) (cosetG D n g s s₀) 𝔽 :=
  Matrix.reindex (Equiv.refl _) (fin_equiv_coset D n g s s₀ k_le_n)
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


open Matrix in
noncomputable def f_succ'
  (f : evalDomainSigma D g s i → 𝔽) (z : 𝔽) (k_le_n : ∑ j', ↑(s j') ≤ n)
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
  (pows z _ *ᵥ VDMInv D n g s s₀ k_le_n *ᵥ Finset.restrict (cosetG D n g s s₀) f) ()

lemma claim_8_1
  {f : ReedSolomon.code (domainEmb D g (i := ∑ j' ∈ finRangeTo i, s j'))
                        (2 ^ (n - (∑ j' ∈ finRangeTo i, (s j' : ℕ))))}
  {z : 𝔽}
  (k_le_n : ∑ j', ↑(s j') ≤ n)
  :
  f_succ' D n g s f.val z k_le_n ∈
    (ReedSolomon.code
      (CosetDomain.domainEmb D g)
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

noncomputable def oracleImpl
    (l : ℕ) (z : Fin (k + 1) → 𝔽) (f : (CosetDomain.evalDomain D g 0) → 𝔽) :
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
              unfold OracleInterface.instDefault Spec.FinalOracleStatement
              rw [h]
              simp
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
        (CosetDomain.domainEmb (i := 0) D g)
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

instance instFinRangeOfAppend {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [FiniteRange [pSpec₁.Challenge]ₒ] [FiniteRange [pSpec₂.Challenge]ₒ] :
  FiniteRange [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ := sorry

-- set_option diagnostics true
instance {t l : ℕ} :
 ([]ₒ ++ₒ
      [((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
            (Spec.pSpecFold D g k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
              Spec.QueryRound.pSpec D g l)).Challenge]ₒ).FiniteRange := sorry
  -- refine @OracleSpec.instFiniteRangeSumAppend (h₁ := inferInstance) (h₂ := ?_) ..
  -- refine @instFinRangeOfAppend _ _ _ _ ?_ ?_
  -- · unfold BatchedFri.Spec.BatchingRound.batchSpec Challenge OracleInterface.toOracleSpec
  --   simp only [Fin.vcons_fin_zero, Nat.reduceAdd, ChallengeIdx]
  --   constructor
  --   · intros i
  --     unfold OracleSpec.range
  --     simp only
  --     rcases i with ⟨i, h⟩
  --     have : i = 0 := by omega
  --     subst this
  --     simp
  --     unfold OracleInterface.Response challengeOracleInterface
  --     simp only
  --     unfold Challenge
  --     simp
  --     haveI : Inhabited 𝔽 := ⟨0⟩
  --     infer_instance
  --   · intros i
  --     unfold OracleSpec.range
  --     simp only
  --     rcases i with ⟨i, h⟩
  --     have : i = 0 := by omega
  --     subst this
  --     simp
  --     unfold OracleInterface.Response challengeOracleInterface
  --     simp only
  --     unfold Challenge
  --     simp
  --     haveI : Inhabited 𝔽 := ⟨0⟩
  --     infer_instance
  -- · refine @instFinRangeOfAppend _ _ _ _ ?_ ?_
  --   · refine @instFinRangeOfAppend _ _ _ _ ?_ ?_
  --     unfold Spec.pSpecFold Challenge OracleInterface.toOracleSpec
  --     constructor
  --     · intros i
  --       unfold OracleSpec.range
  --       simp only
  --       rcases i with ⟨i, h⟩
  --       have : i = 0 := by omega
  --       subst this
  --       simp
  --       unfold OracleInterface.Response challengeOracleInterface
  --       simp only
  --       unfold Challenge
  --       simp
  --       haveI : Inhabited 𝔽 := ⟨0⟩
  --       infer_instance








  -- refine { range_inhabited' := ?_, range_fintype' := ?_ }
  -- refine fun i ↦ ?_
  -- rcases i with i | i
  -- · rcases i
  -- ·

-- #check Equiv.finite_iff

open ENNReal in
lemma lemma_8_3
  {t l m : ℕ}
  (f : Fin t.succ → (CosetDomain.evalDomain D g 0 → 𝔽))
  (m_ge_3 : m ≥ 3)
  :
    let ρ_sqrt :=
      ReedSolomonCode.sqrtRate
        (2 ^ n)
        (CosetDomain.domainEmb (i := 0) D g)
    let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / 2 * m))
    let εC : ℝ≥0∞ := ENNReal.ofReal <|
      (m + (1 : ℚ)/2)^7 * (2^n)^2
        / (2 * ρ_sqrt ^ 3) * (Fintype.card 𝔽)
      + (∑ i, (s i).1) * (2 * m + 1) * (2 ^ n + 1) / (Fintype.card 𝔽 * ρ_sqrt)
    (∃ prov : OracleProver (WitOut := Unit) ..,
        [fun _ => True |
          OracleReduction.run () f ()
            ⟨
              prov,
              (BatchedFri.Spec.batchedFRIreduction (n := n) D g k s d domain_size_cond l t).verifier
            ⟩
         ] > εC + α ^ l) →
      ProximityGap.correlatedAgreement
        (ReedSolomon.code (CosetDomain.domainEmb (i := 0) D g) (2 ^ n)).carrier
        α f := by
  sorry

end Fri
end Fri
