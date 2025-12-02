/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann Quang Dao
-/

import VCVio
import ArkLib.Data.GroupTheory.PrimeOrder
import ArkLib.Data.Classes.Serde
import ArkLib.Data.UniPoly.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-
  # Hardness Assumptions

  This file contains hardness assumptions for commitment schemes.
  These Hardness Assumptions are used to prove the security of commitment schemes.
-/

variable {ι : Type} (oSpec : OracleSpec ι)

open OracleComp OracleSpec
open scoped NNReal

namespace Groups

section PrimeOrder

variable {G : Type} [Group G] {p : outParam ℕ} [hp : Fact (Nat.Prime p)] [PrimeOrderWith G p]
  {g : G}


section Pairings

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [DecidableEq Gₜ]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)]
  (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))

-- TODO this should be a fact in VCV-io I think..
variable [OracleComp.SelectableType (ZMod p)]

/-- The vector of length `n + 1` that consists of powers:
  `#v[1, g, g ^ a.val, g ^ (a.val ^ 2), ..., g ^ (a.val ^ n)` -/
def towerOfExponents (g : G) (a : ZMod p) (n : ℕ) : Vector G (n + 1) :=
  .ofFn (fun i => g ^ (a.val ^ i.val))

/-- The `srs` (structured reference string) for the KZG commitment scheme with secret exponent `a`
    is defined as `#v[g₁, g₁ ^ a, g₁ ^ (a ^ 2), ..., g₁ ^ (a ^ (n - 1))], #v[g₂, g₂ ^ a]` -/
def generateSrs (n : ℕ) (a : ZMod p) : Vector G₁ (n + 1) × Vector G₂ 2 :=
  (towerOfExponents g₁ a n, towerOfExponents g₂ a 1)

/-- The ARSDH adversary returns a set of size D+1 and two group elements h₁ and h₂ upon receiving
the srs. -/
def ARSDHAdversary (D : ℕ) :=
  Vector G₁ (D + 1) × Vector G₂ 2 → OracleComp oSpec (Finset (ZMod p) × G₁ × G₁)

def ARSDHGame (D : ℕ) (adversary : ARSDHAdversary oSpec D (G₁ := G₁) (G₂ := G₂) (p := p)) :
    OracleComp (unifSpec ++ₒ oSpec) (ZMod p × Finset (ZMod p) × G₁ × G₁) := do
  let τ ← liftComp ($ᵗ (ZMod p)) (unifSpec ++ₒ oSpec)
  let srs := generateSrs (g₁ := g₁) (g₂ := g₂) D τ
  let (S, h₁, h₂) ← liftComp (adversary srs) _
  return (τ, S, h₁, h₂)

def ARSDHCond (D : ℕ) (τ : ZMod p) (S : Finset (ZMod p)) (h₁ h₂ : G₁) : Prop
  := letI Zₛ := ∏ s ∈ S, (Polynomial.X - Polynomial.C s)
    S.card = D + 1 ∧ h₁ ≠ 1 ∧ h₂ = h₁ ^ (1 / Zₛ.eval τ).val

/-- The adaptive rational strong Diffie–Hellman (ARSDH) assumption.
Taken from Def. 9.6 in "On the Fiat–Shamir Security of Succinct Arguments from Functional
Commitments" (see https://eprint.iacr.org/2025/902.pdf)
-/
def ARSDH [(unifSpec ++ₒ oSpec).FiniteRange]
    (D : ℕ) (adversary : ARSDHAdversary oSpec D (G₁ := G₁) (G₂ := G₂) (p := p)) (error : ℝ≥0)
    : Prop :=
  [fun (τ,S,h₁,h₂) => ARSDHCond D τ S h₁ h₂
  | ARSDHGame (oSpec := oSpec) (g₁ := g₁) (g₂ := g₂) D adversary
  ] ≤ error

end Pairings

end PrimeOrder

end Groups
