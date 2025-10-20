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

open Code ReedSolomonCode ProbabilityTheory

section Defs

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
noncomputable def divergence (U V : Set (ι → F)) : ℚ≥0 :=
  haveI : Fintype (possibleDeltas U V) := @Fintype.ofFinite _ finite_possibleDeltas
  if h : (possibleDeltas U V).Nonempty
  then (possibleDeltas U V).toFinset.max' (Set.toFinset_nonempty.2 h)
  else 0

end Defs

section Theorems

-- For theorems, since we are using the probability notation `Pr_{let x ← $ᵖ S}[...]` which is
-- not universe-polymorphic, we need to put everything in `Type` and not `Type*`.

variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Fintype F] [Field F]
         {U V C : Set (ι → F)}

open Classical in
/-- `Corollary 1.3` (Concentration bounds) from [BCIKS20]. -/
lemma concentration_bounds {deg : ℕ} {domain : ι ↪ F}
  {U : AffineSubspace F (ι → F)} [Nonempty U]
  (hdiv_pos : 0 < (divergence U (RScodeSet domain deg) : ℝ≥0))
  (hdiv_lt : (divergence U (RScodeSet domain deg) : ℝ≥0) < 1 - ReedSolomonCode.sqrtRate deg domain)
  : let δ' := divergence U (RScodeSet domain deg)
    Pr_{let y ← $ᵖ U}[Code.relHammingDistToCode y (RScodeSet domain deg) ≠ δ']
    ≤ errorBound δ' deg domain := by sorry

end Theorems

end DivergenceOfSets
