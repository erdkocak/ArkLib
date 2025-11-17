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
variable (D : Subgroup 𝔽ˣ) {n : ℕ} [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (g : 𝔽ˣ)
variable (s : Fin (n + 1) → ℕ+) (d : ℕ+)
variable (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)

noncomputable local instance : Fintype 𝔽 := Fintype.ofFinite _

@[simp]
private lemma sum_add_one {i : Fin (n + 1)} {f : Fin (n + 1) → ℕ} :
  ∑ j' ∈ finRangeTo (i + 1), f j' = (∑ j' ∈ finRangeTo i, f j') + f i := by
  unfold finRangeTo
  suffices ∑ x ∈ insert i (List.take i (List.finRange (n + 1))).toFinset, f x =
           ∑ x ∈ (List.take i (List.finRange (n + 1))).toFinset, f x + f i by
    simpa [List.take_add]
  have : i ∉ (List.take i (List.finRange (n + 1))).toFinset := by
    aesop (add simp List.mem_iff_getElem) (add safe (by grind [cases Fin]))
  simp +arith [Finset.sum_insert this]

private lemma roots_of_unity_lem {s : Fin (n + 1) → ℕ+} {i : Fin (n + 1)}
  (k_le_n : ∑ j', (s j' : ℕ) ≤ n) :
  ∑ j' ∈ finRangeTo i, (s j' : ℕ) ≤ n - (s i : ℕ) := by
    apply Nat.le_sub_of_add_le
    rw [←sum_add_one]
    transitivity
    · exact sum_le_univ_sum_of_nonneg (by simp)
    · exact k_le_n

instance {F : Type} [Field F] {a : F} [inst : NeZero a] : Invertible a where
  invOf := a⁻¹
  invOf_mul_self := by field_simp [inst.out]
  mul_invOf_self := by field_simp [inst.out]

@[grind]
def cosetElems {i : Fin (n + 1)} (s₀ : evalDomainSigma D g s i) : List (evalDomainSigma D g s i) :=
    if k_le_n : ∑ j', (s j').1 ≤ n
    then
      (Domain.rootsOfUnity D n (s i)).map fun r =>
        ⟨
          _,
          CosetDomain.mul_root_of_unity D (roots_of_unity_lem k_le_n) s₀.2 r.2
        ⟩ 
    else []

def cosetG {i : Fin (n + 1)} (s₀ : evalDomainSigma D g s i) : Finset (evalDomainSigma D g s i) :=
  (cosetElems D g s s₀).toFinset

def pows (z : 𝔽) (ℓ : ℕ) : Matrix Unit (Fin ℓ) 𝔽 :=
  Matrix.of <| fun _ j => z ^ j.val

def VDM {i : Fin (n + 1)} (s₀ : evalDomainSigma D g s i) :
  Matrix (Fin (2 ^ (s i : ℕ))) (Fin (2 ^ (s i : ℕ))) 𝔽 :=
  if k_le_n : (∑ j', (s j').1) ≤ n
  then
    have : (cosetElems D g s s₀).length = 2 ^ (s i : ℕ) := by
      unfold cosetElems Domain.rootsOfUnity
      simp [k_le_n, PNat.val]
    let v : Fin (2 ^ (s i).1) → 𝔽 :=
      fun x => ((cosetElems D g s s₀).get ⟨x.1, by rw [this]; exact x.2⟩).1.1
    Matrix.vandermonde v
  else 1

def fin_equiv_coset {i : Fin (n + 1)} (s₀ : evalDomainSigma D g s i) : (Fin (2 ^ (s i).1)) ≃ { x // x ∈ cosetG D g s s₀ } where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

lemma pow_eq {G : Type} [Group G] {a b : ℕ} {g : G} :
  a < orderOf g → b < orderOf g → g ^ a = g ^ b → a = b := by
  intros h₁ h₂ h₃
  rwa [pow_inj_mod, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at h₃

instance {i : Fin (n + 1)} (s₀ : evalDomainSigma D g s i) : Invertible (VDM D g s s₀) := by
  haveI : NeZero (VDM D g s s₀).det := by
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
              @Finset.single_le_sum (Fin (n + 1)) ℕ _ _ _
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
              @Finset.single_le_sum (Fin (n + 1)) ℕ _ _ _
                (fun i => (s i).1) Finset.univ (by intros i _; simp)
                i (by simp)
            simp only at this
            exact this
        rw [this, pow_add, mul_comm, Nat.gcd_mul_left_left]
        simp
        rfl
    · simp
  apply @Matrix.invertibleOfDetInvertible


def VDMInv {i : Fin (n + 1)} (s₀ : evalDomainSigma D g s i) :
    Matrix (Fin (2 ^ (s i).1)) { x // x ∈ cosetG D g s s₀ } 𝔽 :=
  Matrix.reindex (Equiv.refl _) (fin_equiv_coset D g s s₀)
    (instInvertibleMatrixFinHPowNatOfNatValVDM D g s s₀).invOf

lemma g_elem_zpower_iff_exists_nat {G : Type} [Group G] [Finite G] {gen g : G} :
    g ∈ Subgroup.zpowers gen ↔ ∃ n : ℕ, g = gen ^ n ∧ n < orderOf gen := by
  apply Iff.intro
  · intros h
    rw [Subgroup.mem_zpowers_iff] at h
    rcases h with ⟨k, h⟩
    have : gen ^ k = gen ^ (k % orderOf gen) :=
      Eq.symm (zpow_mod_orderOf gen k)
    have : ∃ n : ℕ, g = gen ^ n ∧ n < orderOf gen := by
      have pow_pos : 0 ≤ (k % (orderOf gen)) := by
        apply Int.emod_nonneg k
        apply Int.ofNat_ne_zero.mpr
        intros h
        have := h ▸ orderOf_pos gen
        simp at this
      have h' : ∃ n : ℕ, n = k % (orderOf gen) := by
        match h' : k % ↑(orderOf gen) with
        | .ofNat n => use n; rw [h']; rfl
        | .negSucc _ =>
          rw [h'] at pow_pos
          simp at pow_pos
      rcases h' with ⟨n, h'⟩
      rw [←h', zpow_natCast] at this
      use n
      rw [←this]
      refine ⟨h.symm, ?_⟩
      have {a b : ℕ} : (a : ℤ) < (b : ℤ) → a < b := by
        rw [Int.ofNat_lt]
        exact id
      apply this
      rw [h']
      apply Int.emod_lt_of_pos k
      apply Int.natCast_pos.mpr
      exact orderOf_pos gen
    rcases this with ⟨n, this⟩
    use n
  · rintro ⟨n, h⟩
    rw [h.1]
    exact Subgroup.npow_mem_zpowers _ _

open Matrix in
noncomputable def f_succ' {i : Fin (n + 1)}
  (f : evalDomainSigma D g s i → 𝔽) (z : 𝔽)
  (s₀' : evalDomainSigma D g s (i.1 + 1)) : 𝔽 :=
  have :
    ∃ s₀ : evalDomain D g (∑ j' ∈ finRangeTo (i.1), ↑(s j')),
      s₀.1 ^ (2 ^ (s i).1) = s₀'.1 := by
    have h := s₀'.2
    simp only [evalDomain, finRangeTo] at h
    have :
      ((g ^ 2 ^ ∑ j' ∈ (List.take (i.1 + 1) (List.finRange (n + 1))).toFinset, (s j').1))⁻¹ * s₀'.1 ∈
        Domain.evalDomain D (∑ j' ∈ (List.take (↑i + 1) (List.finRange (n + 1))).toFinset, ↑(s j'))
        := by sorry
    simp only [Domain.evalDomain] at this
    rw [g_elem_zpower_iff_exists_nat] at this
    rcases this with ⟨m, this⟩







    sorry
  let s₀ := Classical.choose this
  (pows z _ *ᵥ VDMInv D g s s₀ *ᵥ Finset.restrict (cosetG D g s s₀) f) ()

lemma claim_8_1
  {i : Fin (n + 1)}
  {f : ReedSolomon.code (injectF (i := ∑ j' ∈ finRangeTo i, s j'))
                        (2 ^ (n - (∑ j' ∈ finRangeTo i, (s j' : ℕ))))}
  {z : 𝔽}
  :
  f_succ' D g s f.val z ∈
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

noncomputable def oracle (l : ℕ) (z : Fin (n + 1) → 𝔽) (f : (CosetDomain.evalDomain D g 0) → 𝔽) :
  QueryImpl
    ([]ₒ ++ₒ ([Spec.FinalOracleStatement D g s]ₒ ++ₒ [(Spec.QueryRound.pSpec D g l).Message]ₒ))
    (OracleComp [(Spec.QueryRound.pSpec D g l).Message]ₒ) where
      impl :=
        fun q ↦
          match q with
          | query (.inl i) _ => PEmpty.elim i
          | query (.inr (.inl i)) dom =>
            let f0 := Lagrange.interpolate Finset.univ (fun v => v.1.1) f
            let chals : List (Fin (n + 1) × 𝔽) :=
              ((List.finRange (n + 1)).map (fun i => (i, z i))).take i.1
            let fi : 𝔽[X] := List.foldl (fun f (i, α) => Polynomial.foldNth (s i) f α) f0 chals
            if h : i.1 = n + 1
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
            (z : Fin (n + 1) → 𝔽) :=
      Pr_{let samp ←$ᵖ (CosetDomain.evalDomain D g 0)}[
        [
          fun _ => True |
          (
            (do
              simulateQ (oracle D g s 1 z (fun v ↦ f 0 v + ∑ i, x i * f i.succ v))
                (
                  (
                    Fri.Spec.QueryRound.queryVerifier D g
                      (n := n + 1) (k := n) (s := s) (l := 1)
                        (by
                          apply Spec.round_bound (d := d)
                          transitivity
                          · exact domain_size_cond
                          · apply pow_le_pow (by decide) (by decide)
                            simp
                        )
                  ).verify
                  z
                  (fun i => by
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
    Pr_{let x ←$ᵖ (Fin t → 𝔽); let z ←$ᵖ (Fin (n + 1) → 𝔽)}[ εQ x z ≤ α0 ] ≤ εC
  := by sorry

end Fri
end Fri
