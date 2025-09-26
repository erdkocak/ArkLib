/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ProximityGap
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

open NNReal ProximityGap

/-!
  # Definitions and Theorems about Divergence of Sets

  [BCIKS20] refers to the paper "Proximity Gaps for Reed-Solomon Codes" by Eli Ben-Sasson,
  Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
-/

namespace DivergenceOfSets

noncomputable section

open Code ReedSolomonCode ProbabilityTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*} [DecidableEq F]
         {U V C : Set (ι → F)}

/-- The set of possible relative Hamming distances between two sets. -/
def possibleDeltas (U V : Set (ι → F)) : Set ℚ≥0 :=
  {d : ℚ≥0 | ∃ u ∈ U, δᵣ(u,V) = d}

/-- The set of possible relative Hamming distances between two sets is well-defined. -/
@[simp]
lemma possibleDeltas_subset_relHammingDistRange :
  possibleDeltas U C ⊆ relHammingDistRange ι :=
  fun _ _ ↦ by aesop (add simp possibleDeltas)

/-- The set of possible relative Hamming distances between two sets is finite. -/
@[simp]
lemma finite_possibleDeltas : (possibleDeltas U V).Finite :=
  Set.Finite.subset finite_relHammingDistRange possibleDeltas_subset_relHammingDistRange

open Classical in
/-- Definition of divergence of two sets from `Section 1.2` in [BCIKS20]. -/
def divergence (U V : Set (ι → F)) : ℚ≥0 :=
  haveI : Fintype (possibleDeltas U V) := @Fintype.ofFinite _ finite_possibleDeltas
  if h : (possibleDeltas U V).Nonempty
  then (possibleDeltas U V).toFinset.max' (Set.toFinset_nonempty.2 h)
  else 0

open Classical in
/-- `Corollary 1.3` (Concentration bounds) from [BCIKS20]. -/
lemma concentration_bounds [Fintype F] [Field F] [Fintype ι] {deg : ℕ} {domain : ι ↪ F}
  {U : AffineSubspace F (ι → F)} [Nonempty U]
  (hdiv : (divergence U (RScodeSet domain deg) : ℝ≥0) ≤ 1 - ReedSolomonCode.sqrtRate deg domain)
  : let δ' := divergence U (RScodeSet domain deg)
    Pr_{let y ← $ᵖ U}[Code.relHammingDistToCode y (RScodeSet domain deg) ≠ δ']
    ≤ errorBound δ' deg domain := by sorry

end
end DivergenceOfSets
