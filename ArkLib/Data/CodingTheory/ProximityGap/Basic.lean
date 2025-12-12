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
open scoped ProbabilityTheory
open scoped BigOperators LinearCode
open Code Affine

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

/-- **`(δ, ε)`-CA for low-degree parameterised (polynomial) curves**: Generalized statement of
**Theorem 1.5, [BCIKS20]**
For `k+1` words `u₀, u₁, ..., uₖ ∈ A^ι` let `curve(u) = {∑_{i ∈ {0, ..., k}}, z^i • u_i | z ∈ 𝔽}`
be a low-degree parameterised polynomial curve. If the probability that a random point in
`curve(u)` is `δ`-close to `C` exceeds `k * ε` (not `(k+1) * ε`), then the words `u₀, ..., uₖ`
have correlated agreement.
**NOTE**: this definition could be converted into the form of Pr_{let r ← $ᵖ F}[...] if we want:
  + consistency with `δ_ε_correlatedAgreementAffineLines`
  + making `A` be of arbitrary type universe (Type*)
  + to be able to support the `proximity generator` notation.
-/
noncomputable def δ_ε_correlatedAgreementCurves {k : ℕ}
    {A : Type 0} [AddCommMonoid A] [Module F A] [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (δ ε : ℝ≥0) : Prop :=
  ∀ (u : WordStack (A := A) (κ := Fin (k + 1)) (ι := ι)),
    Pr_{let y ← $ᵖ (Curve.polynomialCurveFinite (F := F) (A := A) u)}[ δᵣ(y.1, C) ≤ δ ] > k * ε
      → jointAgreement (F := A) (κ := Fin (k + 1)) (ι := ι) (C := C) (W := u) (δ := δ)

/-- **`(δ, ε)`-CA for affine spaces**: Generalized statement of **Theorem 1.6, [BCIKS20]**
For `k+1` words `u₀, u₁, ..., uₖ ∈ A^ι` let `U = u₀ + span{u₁, ..., uₖ} ⊂ A^ι` be an affine subspace
(note that `span` here means linear span, so this formulation is not same as the default
affine span/affine hull). If the probability that a random point in `U` is `δ`-close to `C`
exceeds `ε`, then the words `u₀, u₁, ..., uₖ` have correlated agreement. -/
noncomputable def δ_ε_correlatedAgreementAffineSpaces
    {A : Type 0} [AddCommGroup A] [Module F A] [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (δ ε : ℝ≥0) : Prop :=
  ∀ (u : WordStack (A := A) (κ := Fin (k + 1)) (ι := ι)),
    Pr_{let y ← $ᵖ (affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))}[ δᵣ(y.1, C) ≤ δ ] > ε →
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
