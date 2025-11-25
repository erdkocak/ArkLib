/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.GuruswamiSudan
import ArkLib.Data.CodingTheory.Prelims
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.RationalFunctions
import ArkLib.Data.Probability.Notation
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Proximity gap fundamental definitions

Define the fundamental definitions for proximity gap properties of generic codes and
module codes over (scalar) rings.

## Main Definitions

### Proximity Gap Definitions
- `proximityMeasure`: Counts vectors close to linear combinations with code `C`
- `proximityGap`: Proximity gap property at distance `d` with cardinality bound
- `δ_ε_proximityGap`: Generic `(δ, ε)`-proximity gap for any collection of sets

### Correlated Agreement Definitions
- `jointAgreement`: Words collectively agree with code `C` on the same coordinate set
- `jointAgreement_iff_jointProximity`: Equivalence between agreement and proximity formulations
- `δ_ε_correlatedAgreementAffineLines`: Correlated agreement for affine lines (2 words)
- `δ_ε_correlatedAgreementCurves`: Correlated agreement for parametrised curves (k words)
- `δ_ε_correlatedAgreementAffineSpaces`: Correlated agreement for affine subspaces (k+1 words)

## TODOs
- weighted correlated agreement
- mutual correlated agreement
- generalize the CA definitions using proximity generator?

## References

- [BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed–Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654, version 20210703:203025.

- [DG25] Benjamin E. Diamond and Angus Gruen. “Proximity Gaps in Interleaved Codes”. In: IACR
  Communications in Cryptology 1.4 (Jan. 13, 2025). issn: 3006-5496. doi: 10.62056/a0ljbkrz.

-/

namespace ProximityGap

open NNReal Finset Function
open scoped BigOperators
open NNReal Finset Function ProbabilityTheory Finset
open scoped BigOperators LinearCode
open Code

universe u v w k l

open scoped Affine
section CoreSecurityDefinitions
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type k} {ι : Type l} [Fintype κ] [Fintype ι] [Nonempty ι]
-- κ => row indices, ι => column indices
variable {F : Type v} [Ring F] [Fintype F] [DecidableEq F]
-- variable {M : Type} [Fintype M] -- Message space type
variable {A : Type w} [Fintype A] [DecidableEq A] [AddCommMonoid A] [Module F A] -- Alphabet type
variable (C : Set (ι → A))

/-- The proximity measure of two vectors `u` and `v` from a code `C` at distance `d` is the number
  of vectors at distance at most `d` from the linear combination of `u` and `v` with coefficients
  `r` in `F`. -/
noncomputable def proximityMeasure (u v : Word A ι) (d : ℕ) : ℕ :=
  Fintype.card {r : F | Δ₀(r • u + (1 - r) • v, C) ≤ d}

/-- A code `C` exhibits proximity gap at distance `d` and cardinality bound `bound` if for every
      pair of vectors `u` and `v`, whenever the proximity measure for `C u v d` is greater than
      `bound`, then the distance of `[u | v]` from the interleaved code `C ^⊗ 2` is at most `d`. -/
def proximityGap (d : ℕ) (bound : ℕ) : Prop :=
  ∀ u v : Word (A := A) (ι := ι), (proximityMeasure (F := F) C u v d > bound)
    →
    letI : Fintype (C ^⋈ (Fin 2)) := interleavedCodeSet_fintype (C := C)
    (Δ₀(u ⋈₂ v, C ^⋈ (Fin 2)) ≤ d)

/-- The consequent of correlated agreement: Words collectively agree on the same set of coordinates
`S` with the base code `C`.
Variants of this definition **should follow the naming conventions of `jointProximity`**
if possible, for consistency.
TOOD: this can generalize further to support the consequent of mutual correlated agreement. -/
def jointAgreement {κ ι : Type*} [Fintype ι] [DecidableEq F] [DecidableEq ι]
    (C : Set (ι → F)) (δ : ℝ≥0) (W : κ → ι → F) : Prop :=
  ∃ S : Finset ι, #(S) ≥ (1 - δ) * (Fintype.card ι) ∧
    ∃ v : κ → ι → F, ∀ i, v i ∈ C ∧ S ⊆ Finset.filter (fun j => v i j = W i j) Finset.univ

open InterleavedCode in
omit [Ring F] [Fintype F] [DecidableEq F] in
/-- Equivalence between the agreement-based definition `jointAgreement` and
the distance/proximity-based definition `jointProximity` (the latter is represented in
upperbound of interleaved-code distance). -/
@[simp]
theorem jointAgreement_iff_jointProximity
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι] [DecidableEq F] [DecidableEq ι]
    (C : Set (ι → F)) (u : WordStack F κ ι) (δ : ℝ≥0) :
    jointAgreement (C := C) δ u  ↔ jointProximity (C := C) u δ := by
  let e : ℕ := Nat.floor (δ * Fintype.card ι)
  constructor
  · -- Forward direction: jointAgreement → jointProximity
    intro h_words
    rcases h_words with ⟨S, hS_card, v, hv⟩
    -- We have: |S| ≥ (1-δ)*|ι| and ∀ i, v i ∈ MC and S ⊆ {j | v i j = u i j}
    -- Need to show: δᵣ(u_interleaved, MC.interleavedCode) ≤ δ
    -- Define interleaved word from u
    let u_interleaved : InterleavedWord F κ ι := ⋈|u
    -- Construct interleaved codeword from v
    let v_interleaved : InterleavedWord F κ ι := interleaveWordStack v
    have hv_interleaved_mem : v_interleaved ∈ interleavedCodeSet C := by
      rw [mem_interleavedCode_iff]
      intro k
      exact (hv k).1
    -- Now show that u_interleaved and v_interleaved agree on S
    -- This gives us the distance bound
    have h_agree_on_S : ∀ j ∈ S, u_interleaved j = getSymbol v_interleaved j := by
      intro j hj
      ext k
      -- u_interleaved j k = u k j, v_interleaved j k = v k j; Need: u k j = v k j
      have h_agree := (hv k).2
      have hj_in_filter : j ∈ Finset.filter (fun j => v k j = u k j) Finset.univ := by
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_univ j
        · -- v k j = u k j
          have h_subset := Finset.subset_iff.mp h_agree
          have hj_mem : j ∈ S := hj
          let res := h_subset (x := j) hj_mem
          simp only [mem_filter, mem_univ, true_and] at res
          exact res
      simp only [Finset.mem_filter] at hj_in_filter
      exact hj_in_filter.2.symm
    -- From agreement on S, we get distance bound
    have h_dist : δᵣ(u_interleaved, v_interleaved) ≤ δ := by
      rw [relCloseToWord_iff_exists_agreementCols]
      use S
      rw [relDist_floor_bound_iff_complement_bound]
      constructor
      · exact hS_card
      · intro j
        constructor
        · intro hj_in_S
          have h_agree := h_agree_on_S j hj_in_S
          exact h_agree
        · intro hj_not_in_S
          by_contra hj_in_S
          exact hj_not_in_S (h_agree_on_S j hj_in_S)
    rw [←ENNReal.coe_le_coe] at h_dist
    -- Since v_interleaved ∈ MC.interleavedCode, we have δᵣ(u_interleaved, MC.interleavedCode) ≤ δ
    unfold jointProximity
    have h_min_dist : δᵣ(u_interleaved, interleavedCodeSet C) ≤ δᵣ(u_interleaved, v_interleaved)
      := by
      apply relDistFromCode_le_relDist_to_mem (u := u_interleaved) (C := interleavedCodeSet C)
        (v := v_interleaved) (hv := hv_interleaved_mem)
    exact le_trans h_min_dist h_dist
  · -- Backward direction: jointProximity → jointAgreement
    intro h_joint
    unfold jointProximity at h_joint
    let u_interleaved : InterleavedWord F κ ι := ⋈|u
    -- h_joint says: δᵣ(u_interleaved, MC.interleavedCode) ≤ δ
    -- This means there exists v in the interleaved code with δᵣ(u_interleaved, v) ≤ δ
    have h_close := Code.closeToCode_iff_closeToCodeword_of_minDist
      (C := (interleavedCodeSet C)) (u := u_interleaved)
    -- Convert relative distance to natural distance
    -- Key: if δᵣ(u, C) ≤ δ, there exists a codeword v with δᵣ(u, v) ≤ δ
    have h_rel_to_nat : δᵣ(u_interleaved, interleavedCodeSet C) ≤ δ →
        ∃ v ∈ (interleavedCodeSet C), δᵣ(u_interleaved, v) ≤ δ := by
      intro h_rel
      rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at h_rel
      exact h_rel
    have h_exists_v := h_rel_to_nat h_joint
    rcases h_exists_v with ⟨v, hv_mem, hv_dist⟩
    -- Now convert relative distance to agreement set
    -- We need: δᵣ(u_interleaved, v) ≤ δ → ∃ S, |S| ≥ (1-δ)*|ι| and agreement
    -- Convert relative distance δ to natural distance e
    have h_nat_dist : Δ₀(u_interleaved, v) ≤ e := by
      rw [pairRelDist_le_iff_pairDist_le (δ := δ)] at hv_dist
      exact hv_dist
    have h_agree := Code.closeToWord_iff_exists_agreementCols
      (u := u_interleaved) (v := v) (e := e)
    have h_agree_nat := h_agree.mp h_nat_dist
    rcases h_agree_nat with ⟨S, hS_card, h_agree_S⟩
    -- Now extract rows from v to get v : κ → ι → F
    let v_rows : κ → ι → F := fun k => getRow v k
    use S
    constructor
    · -- Prove |S| ≥ (1-δ)*|ι|
      rw [ge_iff_le]
      rw [relDist_floor_bound_iff_complement_bound] at hS_card
      exact hS_card
    · -- Prove agreement
      use v_rows
      intro i
      constructor
      · -- v_rows i ∈ MC
        simp only [interleavedCodeSet, Set.mem_setOf_eq] at hv_mem
        exact hv_mem i
      · -- S ⊆ {j | v_rows i j = u i j}
        simp only [Finset.subset_iff]
        intro j hj_mem
        simp only [mem_filter, mem_univ, true_and] -- ⊢ v_rows i j = u i j
        have h_agree := h_agree_S (colIdx := j).1 hj_mem
        apply congrArg (fun x => x i) at h_agree
        exact id (Eq.symm h_agree)

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Ring F] [Fintype F] [DecidableEq F]
  {k : ℕ}

/-- Definition 1.1 in [BCIKS20].

Let `P` be a set `P` and `C` a collection of sets. We say that `C` displays a
`(δ, ε)`-proximity gap with respect to `P` and the relative Hamming distance measure
if for every `S ∈ C` exactly one of the following holds:

1. The probability that a randomly sampled element `s` from `S` is `δ`-close to `P` is `1`.
2. The probability that a randomly sampled element `s` from `S` is `δ`-close to `P` is at most
`ε`.

We call `δ` the proximity parameter and `ε` the error parameter. -/
noncomputable def δ_ε_proximityGap {α : Type} [DecidableEq α] [Nonempty α]
  (P : Finset (ι → α)) (C : Set (Finset (ι → α))) (δ ε : ℝ≥0) : Prop :=
  ∀ S ∈ C, ∀ [Nonempty S],
  Xor'
  ( Pr_{let x ← $ᵖ S}[δᵣ(x.val, P) ≤ δ] = 1 )
  ( Pr_{let x ← $ᵖ S}[δᵣ(x.val, P) ≤ δ] ≤ ε )

/-- Definition: `(δ, ε)`-correlated agreement for affine lines.
For every pair of words `u₀, u₁`, if the probability that a random affine line `u₀ + z • u₁` is
`δ`-close to `C` exceeds `ε`, then `u₀` and `u₁` have correlated agreement with `C`.
-- **TODO**: prove that `δ_ε_correlatedAgreementAffineLines` implies `δ_ε_proximityGap`
-/
noncomputable def δ_ε_correlatedAgreementAffineLines
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Module F A]
    (C : Set (ι → A)) (δ ε : ℝ≥0) : Prop :=
  ∀ (u : WordStack (A := A) (κ := Fin 2) (ι := ι)),
    Pr_{let z ← $ᵖ F}[δᵣ(u 0 + z • u 1, C) ≤ δ] > ε →
    jointAgreement (F := A) (κ := Fin 2) (ι := ι) (C := C) (W := u) (δ := δ)

/-- **[Definition 2.3, DG25]** We say that `C ⊂ F^n` features multilinear correlated agreement
with respect to the proximity parameter `δ` and the error bound `ε`, folding degree `ϑ > 0` if:
∀ word stack `u` of size `2^ϑ`, if the probability that
  (a random multilinear combination of the word stack `u` with randomness `r` is `δ`-close to `C`)
  exceeds `ε`, then the word stack `u` has correlated agreement with `C ^⋈ (2^ϑ)`. -/
def δ_ε_multilinearCorrelatedAgreement [CommRing F]
  {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Module F A]
  (C : Set (ι → A)) (ϑ : ℕ) (δ ε : ℝ≥0) : Prop :=
  ∀ (u : WordStack A (Fin (2^ϑ)) ι),
    Pr_{let r ← $ᵖ (Fin ϑ → F)}[ -- This syntax only works with (A : Type 0)
      δᵣ(r |⨂| u, C) ≤ δ
    ] > (ϑ : ℝ≥0) * ε →
    jointAgreement (F := A) (κ := Fin (2 ^ ϑ)) (ι := ι) (C := C) (W := u) (δ := δ)

/-- Definition: `(δ, ε)`-correlated agreement for low-degree parameterised curves.
For every curve passing through words `u₀, ..., uκ`, if the probability that a random point on the
curve is `δ`-close to the code `C` is at most `ε`, then the words `u₀, ..., uκ` have
correlated agreement.
**NOTE**: this definition could be converted into the form of Pr_{let r ← $ᵖ F}[...] if we want:
  + consistency with `δ_ε_correlatedAgreementAffineLines`
  + making `A` be of arbitrary type universe (Type*)
  + to be able to support the `proximity generator` notation.
-/
noncomputable def δ_ε_correlatedAgreementCurves {k : ℕ}
    {A : Type 0} [AddCommMonoid A] [Module F A] [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (δ ε : ℝ≥0) : Prop :=
  ∀ (u : WordStack (A := A) (κ := Fin k) (ι := ι)),
    Pr_{let y ← $ᵖ (Curve.parametrisedCurveFinite (F := F) (A := A) u)}[ δᵣ(y.1, C) ≤ δ ] > ε →
    jointAgreement (F := A) (κ := Fin k) (ι := ι) (C := C) (W := u) (δ := δ)

noncomputable def δ_ε_correlatedAgreementAffineSpaces
    {A : Type 0} [AddCommGroup A] [Module F A] [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (δ ε : ℝ≥0) : Prop :=
  ∀ (u : WordStack (A := A) (κ := Fin (k + 1)) (ι := ι)), -- Affine.instFintypeAffineSubspace
    let affineSubspace : AffineSubspace F (ι → A) :=
      AffineSubspace.mk' (p := u 0) (direction := Submodule.span F (Finset.univ.image (Fin.tail u)))
    Pr_{let y ← $ᵖ (affineSubspace)}[ δᵣ(y.1, C) ≤ δ ] > ε →
    jointAgreement (F := A) (κ := Fin (k + 1)) (ι := ι) (C := C) (W := u) (δ := δ)

end CoreSecurityDefinitions

namespace Trivariate

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]

open Polynomial Bivariate

noncomputable def eval_on_Z₀ (p : (RatFunc F)) (z : F) : F :=
  RatFunc.eval (RingHom.id _) z p

notation3:max R "[Z][X]" => Polynomial (Polynomial R)

notation3:max R "[Z][X][Y]" => Polynomial (Polynomial (Polynomial (R)))

notation3:max "Y" => Polynomial.X
notation3:max "X" => Polynomial.C Polynomial.X
notation3:max "Z" => Polynomial.C (Polynomial.C Polynomial.X)

noncomputable opaque eval_on_Z (p : F[Z][X][Y]) (z : F) : F[X][Y] :=
  p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))

open Polynomial.Bivariate in
noncomputable def toRatFuncPoly (p : F[Z][X][Y]) : (RatFunc F)[X][Y] :=
  p.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))

end Trivariate

end ProximityGap
