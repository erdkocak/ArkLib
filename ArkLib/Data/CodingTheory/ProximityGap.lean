/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.Prelims
import ArkLib.Data.Probability.Notation
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Defs
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.Henselian

/-!
  # Definitions and Theorems about Proximity Gaps

  We define the proximity gap properties of linear codes over finite fields.

  [BCIKS20] refers to the paper "Proximity Gaps for Reed-Solomon Codes" by Eli Ben-Sasson,
  Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.

  ## Main Definitions

-/

universe u

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory

open scoped BigOperators LinearCode

section

variable {n : Type} [Fintype n] [DecidableEq n]

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

variable (C : Submodule F (n → F)) [DecidablePred (· ∈ C)]

/-- The proximity measure of two vectors `u` and `v` from a code `C` at distance `d` is the number
  of vectors at distance at most `d` from the linear combination of `u` and `v` with coefficients
  `r` in `F`. -/
def proximityMeasure (u v : n → F) (d : ℕ) : ℕ :=
  Fintype.card {r : F | Δ₀'(r • u + (1 - r) • v, C) ≤ d}

/-- A code `C` exhibits proximity gap at distance `d` and cardinality bound `bound` if for every
      pair of vectors `u` and `v`, whenever the proximity measure for `C u v d` is greater than
      `bound`, then the distance of `[u | v]` from the interleaved code `C ^⊗ 2` is at most `d`. -/
def proximityGap (d : ℕ) (bound : ℕ) : Prop :=
  ∀ u v : n → F, (proximityMeasure C u v d > bound)
    → (Δ₀( u ⋈ v , C ^⋈ Fin 2 ) ≤ d)

/-- A code `C` exhibits `δ`-correlated agreement with respect to a tuple of vectors `W_1, ..., W_k`
  if there exists a set `S` of coordinates such that the size of `S` is at least `(1 - δ) * |n|`,
  and there exists a tuple of codewords `v_1, ..., v_k` such that `v_i` agrees with `W_i` on `S`
  for all `i`. -/
def correlatedAgreement (C : Set (n → F)) (δ : ℝ≥0) {k : ℕ} (W : Fin k → n → F) : Prop :=
  ∃ S : Finset n, #(S) ≥ (1 - δ) * (Fintype.card n) ∧
    ∃ v : Fin k → n → F, ∀ i, v i ∈ C ∧ {j | v i j = W i j} = S

end

section

variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type}

/-- `Definition 1.1` in [BCIKS20]. -/
noncomputable def generalProximityGap {α : Type} [DecidableEq α] [Nonempty α]
  (P : Finset (ι → α)) (C : Set (Finset (ι → α))) (δ ε : ℝ≥0) : Prop :=
  ∀ S ∈ C, ∀ [Nonempty S],
  Xor'
  ( Pr_{let x ← $ᵖ S}[Code.relHammingDistToCode x.1 P ≤ δ] = 1 )
  ( Pr_{let x ← $ᵖ S}[Code.relHammingDistToCode x.1 P ≤ δ] ≤ ε )
end

section
variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The error bound `ε` in the pair of proximity and error parameters `(δ,ε)` for Reed-Solomon codes
  defined up to the Johnson bound. More precisely, let `ρ` be the rate of the Reed-Solomon code.
  Then for `δ ∈ (0, 1 - √ρ)`, we define the relevant error parameter `ε` for the unique decoding
  bound, i.e. `δ ∈ [0, (1-ρ)/2]` and Johnson bound, i.e. `δ ∈ [(1-ρ)/2 , 1 - √ρ]`. Otherwise,
  we set `ε = 0`.
-/
noncomputable def errorBound (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F) : ℝ≥0 :=
  letI ρ : ℝ≥0 := ρ (ReedSolomon.code domain deg)
  if δ ∈ Set.Ioc 0 ((1 - ρ)/2)
  then Fintype.card ι / Fintype.card F
  else if δ ∈ Set.Ioo ((1 - ρ)/2) (1 - ρ.sqrt)
       then letI m := min (1 - ρ.sqrt - δ) (ρ.sqrt / 20)
            ⟨(deg ^ 2 : ℝ≥0) / ((2 * m) ^ 7 * (Fintype.card F : ℝ)), by positivity⟩
       else 0

/-- `Theorem 1.2` (Proximity Gaps for Reed-Solomon Codes) in [BCIKS20]. -/
theorem proximity_gap_RSCodes {k t : ℕ} [NeZero k] [NeZero t] {deg : ℕ} {domain : ι ↪ F}
  (C : Fin t → (Fin k → (ι → F))) {δ : ℝ≥0} (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)) :
  generalProximityGap
    (ReedSolomonCode.toFinset domain deg)
    (Affine.AffSpanFinsetCol C)
    δ
    (errorBound δ deg domain) := by sorry

set_option linter.style.commandStart false

/-- `Theorem 1.4` (Main Theorem — Correlated agreement over lines) in [BCIKS20]. -/
theorem correlatedAgreement_lines {u : Fin 2 → ι → F} {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  (hproximity :
    Pr_{ let z ← $ᵖ F}[
        Code.relHammingDistToCode (u 0 + z • u 1) (ReedSolomon.code domain deg) ≤ δ
      ] > errorBound δ deg domain
  ) : correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

/-- `Theorem 1.5` (Correlated agreement for low-degree parameterised curves) in [BCIKS20]. -/
theorem correlatedAgreement_affine_curves [DecidableEq ι] {k : ℕ} {u : Fin k → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - ReedSolomonCode.sqrtRate deg domain)
  (hproximity :
    Pr_{let y ← $ᵖ (Curve.parametrisedCurveFinite u)}[
      Code.relHammingDistToCode y.1 (ReedSolomon.code domain deg) ≤ δ
    ] >
      k * (errorBound δ deg domain)) :
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

open Affine in
/-- `Theorem 1.6` (Correlated agreement over affine spaces) in [BCIKS20]. -/
theorem correlatedAgreement_affine_spaces {k : ℕ} [NeZero k] {u : Fin (k + 1) → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  (hproximity :
    Pr_{let y ← $ᵖ (u 0 +ᵥ affineSpan F (Finset.univ.image (Fin.tail u)).toSet)}[
        Code.relHammingDistToCode (ι := ι) (F := F) y (ReedSolomon.code domain deg) ≤ δ
    ] > errorBound δ deg domain) :
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

end
end ProximityGap
