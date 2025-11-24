/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/


import ArkLib.CommitmentScheme.Basic
import ArkLib.AGM.Basic
import ArkLib.Data.UniPoly.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-! ## The KZG Polynomial Commitment Scheme

In this file, we define the KZG polynomial commitment scheme, and prove its correctness and
straightline extraction in the AGM. -/

open UniPoly
open Polynomial

namespace KZG

variable {G : Type} [Group G] {p : outParam ℕ} [hp : Fact (Nat.Prime p)] [PrimeOrderWith G p]
  {g : G}

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [DecidableEq Gₜ]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)]
  (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))

omit [DecidableEq Gₜ] in
lemma lin_fst (g₁ : G₁) (g₂ : G₂) (a : ℤ) : a • (pairing g₁ g₂) =  pairing (g₁ ^ a) (g₂) := by
  change a • (pairing (Additive.ofMul g₁) (Additive.ofMul g₂))
    = pairing (Additive.ofMul (g₁ ^ a)) (Additive.ofMul g₂)
  simp [ofMul_zpow]

omit [DecidableEq Gₜ] in
lemma lin_snd (g₁ : G₁) (g₂ : G₂) (a : ℤ) : a • (pairing g₁ g₂) =  pairing (g₁) (g₂ ^ a) := by
  change a • (pairing (Additive.ofMul g₁) (Additive.ofMul g₂))
    = pairing (Additive.ofMul g₁) (Additive.ofMul (g₂ ^ a))
  simp [ofMul_zpow]

lemma modp_eq (x y : ℤ) (g : G) (hxy : x ≡ y [ZMOD p]) : g ^ x = g ^ y := by
  have hordg : g = 1 ∨ orderOf g = p := by
    have ord_g_dvd : orderOf g ∣ p := by
      have hc : Nat.card G = p := (PrimeOrderWith.hCard : Nat.card G = p)
      simpa [hc] using (orderOf_dvd_natCard g)
    have hdisj : orderOf g = 1 ∨ orderOf g = p := (Nat.dvd_prime hp.out).1 ord_g_dvd
    simpa [orderOf_eq_one_iff] using hdisj
  rcases hordg with ord1 | ordp
  · simp [ord1]
  · have hxmy : (orderOf g : ℤ) ∣ x - y := by
      have hxmy_p : (p : ℤ) ∣ x - y := by
        simpa using (Int.modEq_iff_dvd.mp hxy.symm)
      simpa [ordp] using hxmy_p
    exact (orderOf_dvd_sub_iff_zpow_eq_zpow).1 hxmy

lemma modp_eq_additive (x y : ℤ) (g : Additive G) (hxy : x ≡ y [ZMOD p]) : x • g = y • g := by
  have hxyeq : (Additive.toMul g) ^ x = (Additive.toMul g) ^ y :=
    modp_eq (G:=G) (p:=p) (g:=(Additive.toMul g)) x y hxy
  simpa [ofMul_toMul, ofMul_zpow] using congrArg Additive.ofMul hxyeq

/-- The vector of length `n + 1` that consists of powers:
  `#v[1, g, g ^ a.val, g ^ (a.val ^ 2), ..., g ^ (a.val ^ n)` -/
def towerOfExponents (g : G) (a : ZMod p) (n : ℕ) : Vector G (n + 1) :=
  .ofFn (fun i => g ^ (a.val ^ i.val))

variable {n : ℕ}

/-- The `srs` (structured reference string) for the KZG commitment scheme with secret exponent `a`
    is defined as `#v[g₁, g₁ ^ a, g₁ ^ (a ^ 2), ..., g₁ ^ (a ^ (n - 1))], #v[g₂, g₂ ^ a]` -/
def generateSrs (n : ℕ) (a : ZMod p) : Vector G₁ (n + 1) × Vector G₂ 2 :=
  (towerOfExponents g₁ a n, towerOfExponents g₂ a 1)

/-- One can verify that the `srs` is valid via using the pairing -/
def checkSrs (proveSrs : Vector G₁ (n + 1)) (verifySrs : Vector G₂ 2) : Prop :=
  ∀ i : Fin n,
    pairing (proveSrs[i.succ]) (verifySrs[0]) = pairing (proveSrs[i.castSucc]) (verifySrs[1])

/-- To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of
maximum degree `n`), we compute: `∏ i : Fin (n+1), srs[i] ^ (p.coeff i)` -/
def commit (srs : Vector G₁ (n + 1)) (coeffs : Fin (n + 1) → ZMod p) : G₁ :=
  ∏ i : Fin (n + 1), srs[i] ^ (coeffs i).val

omit [Module (ZMod p) (Additive G₁)] in
/-- The commitment to a mathlib polynomial `poly` of maximum degree `n` is equal to
`g₁ ^ (poly.1.eval a).val` -/
theorem commit_eq {a : ZMod p} (hpG1 : Nat.card G₁ = p)
    (poly : degreeLT (ZMod p) (n + 1)) :
    commit (towerOfExponents g₁ a n) (degreeLTEquiv _ _ poly) = g₁ ^ (poly.1.eval a).val := by
  have {g₁ : G₁} (a b : ℕ) : g₁^a = g₁^b ↔ g₁^(a : ℤ) = g₁^(b : ℤ) := by
    simp only [zpow_natCast]
  simp only [commit, towerOfExponents, Fin.getElem_fin, Vector.getElem_ofFn]
  simp_rw [← pow_mul, Finset.prod_pow_eq_pow_sum,
    eval_eq_sum_degreeLTEquiv poly.property,
      this,
      ←orderOf_dvd_sub_iff_zpow_eq_zpow]

  have hordg₁ : g₁ = 1 ∨ orderOf g₁ = p := by
    have ord_g₁_dvd : orderOf g₁ ∣ p := by rw [← hpG1]; apply orderOf_dvd_natCard
    rw [Nat.dvd_prime hp.out, orderOf_eq_one_iff] at ord_g₁_dvd
    exact ord_g₁_dvd

  rcases hordg₁ with ord1 | ordp
  · simp [ord1]
  · simp [ordp, ←ZMod.intCast_eq_intCast_iff_dvd_sub]
    apply Fintype.sum_congr
    intro x
    exact mul_comm _ _

omit [Module (ZMod p) (Additive G₁)] in
/-- The commitment to a computable polynomial (UniPoly) `poly` of maximum degree `n+1` is equal to
`g₁ ^ (poly.eval a).val`.
Note that the degree of a UniPoly is the mathematical degree + 1 for non-zero polynomials. -/
theorem commit_eq_UniPoly {a : ZMod p} (hpG1 : Nat.card G₁ = p)
    (poly : UniPoly (ZMod p)) (hn : poly.degree ≤ n + 1) :
    commit (towerOfExponents g₁ a n)
    ((coeff poly) ∘ Fin.val)
  = g₁ ^ (poly.eval a).val := by
  have {g₁ : G₁} (a b : ℕ) : g₁^a = g₁^b ↔ g₁^(a : ℤ) = g₁^(b : ℤ) := by
    simp only [zpow_natCast]
  simp only [commit, towerOfExponents, Fin.getElem_fin, Vector.getElem_ofFn]
  simp_rw [← pow_mul, Finset.prod_pow_eq_pow_sum,
      ←eval_toPoly_eq_eval,
      eval_eq_sum,
      this,
      ←orderOf_dvd_sub_iff_zpow_eq_zpow]

  have hordg₁ : g₁ = 1 ∨ orderOf g₁ = p := by
    have ord_g₁_dvd : orderOf g₁ ∣ p := by rw [← hpG1]; apply orderOf_dvd_natCard
    rw [Nat.dvd_prime hp.out, orderOf_eq_one_iff] at ord_g₁_dvd
    exact ord_g₁_dvd

  let f := fun e a_1 ↦ a_1 * a ^ e
  have hf : ∀ (i : ℕ), f i 0 = 0 := by
    intro i
    simp_all only [zero_mul, f]
  have hs : poly.toPoly.support ⊆ Finset.range (n + 1) := by
    have hnatDeg : poly.toPoly.natDegree < (n+1) := by
      by_cases hcoeff: ∃ i, poly.coeff i ≠ 0
      · calc poly.toPoly.natDegree = poly.degree - 1 := by simp_rw [degree_toPoly' hcoeff]
        _ ≤ n := by exact Nat.sub_le_sub_right hn 1
        _ < n + 1 := Nat.lt_succ_self n
      · have hcoeff: ∀i, poly.toPoly.coeff i = 0 := by
          simp_all [coeff_toPoly]
        have hpoly: poly.toPoly = 0 := by
          ext n; exact hcoeff n
        simp [hpoly]
    simp_rw [Polynomial.supp_subset_range hnatDeg]

  rcases hordg₁ with ord1 | ordp
  · simp [ord1]
  · simp [ordp, ←ZMod.intCast_eq_intCast_iff_dvd_sub]
    rw [Polynomial.sum_eq_of_subset
      (R := ZMod p) (S := ZMod p) (p := poly.toPoly)
      f hf (s := Finset.range (n + 1)) hs]
    simp_rw [f, coeff_toPoly, Array.getD_eq_getD_getElem?]
    simp only [mul_comm]
    rw [Fin.sum_univ_eq_sum_range (fun x => a ^ x * poly[x]?.getD 0) (n+1)]


/-- To generate an opening proving that a polynomial `poly` has a certain evaluation at `z`,
  we return the commitment to the polynomial `q(X) = (poly(X) - poly.eval z) / (X - z)` -/
def generateOpening [Fact (Nat.Prime p)] (srs : Vector G₁ (n + 1))
    (coeffs : Fin (n + 1) → ZMod p) (z : ZMod p) : G₁ :=
    letI poly : UniPoly (ZMod p) := UniPoly.mk (Array.ofFn coeffs)
    letI q : UniPoly (ZMod p) := UniPoly.divByMonic (poly - UniPoly.C (poly.eval z))
      (UniPoly.X - UniPoly.C z)
    commit srs (fun i : Fin (n + 1) => q.coeff i)

/-- To verify a KZG opening `opening` for a commitment `commitment` at point `z` with claimed
evaluation `v`, we use the pairing to check "in the exponent" that `p(a) - p(z) = q(a) * (a - z)`,
  where `p` is the polynomial and `q` is the quotient of `p` at `z` -/
def verifyOpening (verifySrs : Vector G₂ 2) (commitment : G₁) (opening : G₁)
    (z : ZMod p) (v : ZMod p) : Bool :=
  pairing (commitment / g₁ ^ v.val) (verifySrs[0]) =
    pairing opening (verifySrs[1] / g₂ ^ z.val)

-- p(a) - p(z) = q(a) * (a - z)
-- e ( C / g₁ ^ v , g₂ ) = e ( O , g₂ ^ a / g₂ ^ z)
theorem correctness (hpG1 : Nat.card G₁ = p) (n : ℕ) (a : ZMod p)
  (coeffs : Fin (n + 1) → ZMod p) (z : ZMod p) :
  let poly : UniPoly (ZMod p) := UniPoly.mk (Array.ofFn coeffs)
  let v : ZMod p := poly.eval z
  let srs : Vector G₁ (n + 1) × Vector G₂ 2 := generateSrs (g₁:=g₁) (g₂:=g₂) n a
  let C : G₁ := commit srs.1 coeffs
  let opening: G₁ := generateOpening srs.1 coeffs z
  verifyOpening pairing (g₁:=g₁) (g₂:=g₂) srs.2 C opening z v := by
  intro poly v
  unfold verifyOpening generateSrs
  simp only [decide_eq_true_eq]

  -- helper facts for the proof

  -- coeffs is the finite coefficients map of poly
  have hcoeffs : coeffs = (coeff poly) ∘ Fin.val := by
    simp_all only [poly]
    ext x : 1
    simp only [Function.comp_apply]
    simp only [Array.getD_eq_getD_getElem?, Array.size_ofFn, Fin.is_lt, getElem?_pos,
    Array.getElem_ofFn, Fin.eta, Option.getD_some]

  -- the (mathematical) degree of poly is less than n+1
  have hpdeg : degree poly ≤ n+1 := by
    simp_rw [←Trim.size_eq_degree]
    apply le_trans (Trim.size_le_size (p := poly))
    simp_rw [poly]
    simp

  -- expansion of (a-z) to Polynomial form
  have haz : (a-z) = UniPoly.eval a (UniPoly.X - UniPoly.C z) := by
    simp_rw [←eval_toPoly_eq_eval, toPoly_sub, eval_sub,
    eval_toPoly_eq_eval]
    simp only [UniPoly.eval_X, UniPoly.eval_C]

  -- the polynomial form of (a-z) is monic
  have hmonic : monic (UniPoly.X - UniPoly.C z) := by
    simp only [UniPoly.monic_X_sub_C]

  -- the proof

  -- restate the commitment as the evaluation of poly at a (C => g₁^poly(a))
  simp_rw [hcoeffs, commit_eq_UniPoly hpG1 poly hpdeg]

  -- define q(X) := (poly(X) - poly(z)) / (X-z)
  -- and restate the opening as the evaluation of q at a (opening => g₁^q(a))
  simp_rw [generateOpening, ←hcoeffs]
  set q := (mk poly - UniPoly.C (UniPoly.eval z (mk poly))).divByMonic (UniPoly.X - UniPoly.C z)
  have hqdeg : degree q ≤ n+1 := by
    calc
      degree q ≤ degree (mk poly - UniPoly.C (UniPoly.eval z (mk poly))) := by
        simp [q, degree_divByMonic hmonic]
      _ ≤ max (degree (mk poly)) (degree (UniPoly.C (UniPoly.eval z (mk poly)))) :=
        UniPoly.degree_sub _ _
      _ ≤ max (n+1) 1 := by
        apply max_le_max
        · exact hpdeg
        · by_cases h0 : UniPoly.eval z (mk poly) = 0
          · simp only [h0, degree_C_zero, zero_le]
          · simp [UniPoly.degree_C (x := UniPoly.eval z (mk poly)) (by simpa using h0)]
      _ = n+1 := by
        simp only [Nat.succ_le_succ (Nat.zero_le n), sup_of_le_left]
  have hfun: (fun i ↦ q.coeff ↑i : Fin (n+1) → ZMod p) = (coeff q) ∘ Fin.val := by rfl
  simp_rw [hfun, commit_eq_UniPoly hpG1 q hqdeg]

  -- evaluate the pairing linearly.
  -- e (g₁^poly(a) / g₂^poly(z), g₂)= e (g₁^q(a), g₂^a / g₂^(z))
  -- => (poly(a) - poly(z)) • e (g₁,g₂) = (q(a) * (a-z)) • e (g₁,g₂)
  simp only [towerOfExponents, Nat.reduceAdd, Vector.getElem_ofFn, pow_zero, pow_one]
  simp_rw [←zpow_natCast_sub_natCast, ←zpow_natCast, ←lin_snd, ←lin_fst, smul_smul]

  -- eliminate the pairing and reason only about the exponents: poly(a) - poly(z) = q(a) * (a-z)
  apply modp_eq_additive
  refine (Int.modEq_iff_dvd).2 ?_
  let x : ℤ := (↑(UniPoly.eval a poly).val) - (↑v.val)
  let y : ℤ := (↑(a.val) - ↑(z.val)) * ↑(UniPoly.eval a q).val
  refine (Iff.mp (ZMod.intCast_eq_intCast_iff_dvd_sub (a := x) (b := y) (c := p))) ?_
  subst x y; simp

  -- unfold q to obtain the self canceling goal:
  -- poly(a) - poly(z) = (poly(a) - poly(z)) / (a-z) * (a-z)
  -- prove the goal using the eval isomorphism to mathlib Polynomials
  subst v q
  simp_rw [haz]
  simp_rw [←eval_toPoly_eq_eval, toPoly_divByMonic hmonic,toPoly_sub, ←eval_mul, toPoly_C, toPoly_X]
  simp_rw [X_sub_C_mul_divByMonic_eq_sub_modByMonic, modByMonic_X_sub_C_eq_C_eval]
  simp only [eval_sub, Polynomial.eval_C, sub_self, map_zero, sub_zero]

open Commitment

-- TODO this should be a fact in VCV-io I think..
variable [OracleComp.SelectableType (ZMod p)]

local instance : OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  Response := ZMod p
  answer := fun coeffs z =>
    let poly : UniPoly (ZMod p) := UniPoly.mk (Array.ofFn coeffs)
    poly.eval z

namespace CommitmentScheme

/-- The KZG instantiated as a **(functional) commitment scheme**.

  The scheme takes a pregenerated srtuctured reference string (srs) for the
  commiter and the verifier (generated by `generateSrs`).

  - `commit` : a function that commits to an `n + 1`-tuple of coefficients `coeffs`
  (corresponding to a polynomial of maximum degree `n`)
  - `opening` : a non-interactive reduction (i.e. soly the committer sends a single
  message) to prove the evaluation of the commited polynomial at a point `z`. The
  message from the prover is the witness for the evaluation.
-/
def KZG :
    Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) Unit G₁ (Vector G₁ (n + 1)) (Vector G₂ 2)
    ⟨!v[.P_to_V], !v[G₁]⟩ where
  keygen := do
    let a ←$ᵗ (ZMod p)
    let srs := generateSrs (g₁:=g₁) (g₂:=g₂) n a
    return srs
  commit := fun ck coeffs _ => return commit ck coeffs
  opening := fun (ck,vk) => {
    prover := {
      PrvState := fun
        | 0 => (Fin (n + 1) → ZMod p) × ZMod p
        | _ => Unit

      input := fun ⟨⟨commitment, z, v⟩, ⟨coefficients, _⟩⟩ =>
        (coefficients, z)

      sendMessage := fun ⟨0, _⟩ => fun (coefficients, z) => do
        let opening := generateOpening ck coefficients z
        return (opening, ())

      receiveChallenge := fun ⟨i, h⟩ => by
        have : i = 0 := Fin.eq_zero i
        subst this
        nomatch h

      output := fun _ => return (true, ())
    }

    verifier := {
      verify := fun ⟨commitment, z, v⟩ transcript => do
        let opening : G₁ := transcript ⟨0, by decide⟩
        return verifyOpening (g₁:=g₁) (g₂:=g₂) pairing vk commitment opening z v
    }
  }

open OracleSpec OracleComp SubSpec ProtocolSpec

/- the KZG satisfies perfect correctness as defined in `CommitmentScheme`
theorem correctness (hpG1 : Nat.card G₁ = p) (a : ZMod p) {g₁ : G₁} {g₂ : G₂} :
    Commitment.perfectCorrectness (pure ()) ⟨isEmptyElim⟩
    (KZG (n:=n) (g₁:=g₁) (g₂:=g₂) (pairing:=pairing)
    (generateSrs (g₁:=g₁) (g₂:=g₂) n a)) := by
    intro data randomness query
    unfold Proof.completeness Reduction.completeness
    have hpSpec : ProverOnly ⟨!v[.P_to_V], !v[G₁]⟩ := by
      refine { prover_first' := ?_ }; simp
    simp only [Reduction.run_of_prover_first]
    simp [KZG]
    intro a_1 a_2 b a_3 a_4 a_5
    change ZMod p at a_2
    change ZMod p at b
    simp [acceptRejectRel]
    set coeffs := a_3
    set z := a_2
    set v := b
    simp only [OracleInterface.answer] at *
    subst a_4 a_5 v
    simpa using KZG.correctness (g₁:=g₁) (g₂:=g₂) (pairing:=pairing) hpG1 n a coeffs z
-/

end CommitmentScheme

end KZG
