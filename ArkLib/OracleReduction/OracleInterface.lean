/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ArkLib.ToVCVio.SimOracle
import ArkLib.Data.MvPolynomial.Notation
import Mathlib.Algebra.Polynomial.Roots
-- import ArkLib.Data.MlPoly.Basic

/-!
  # Definitions and Instances for `OracleInterface`

  We define `OracleInterface`, which is a type class that augments a type with an oracle interface
  for that type. The interface specifies the type of queries, the type of responses, and the
  oracle's behavior for a given underlying element of the type.

  `OracleInterface` is used to restrict the verifier's access to the input oracle statements and the
  prover's messages in an interactive oracle reduction (see `Basic.lean`).

  We define `OracleInterface` instances for common types:

  - Univariate and multivariate polynomials. These instances turn polynomials into oracles for which
    one can query at a point, and the response is the evaluation of the polynomial on that point.

  - Vectors. This instance turns vectors into oracles for which one can query specific positions.
-/

universe u v w

open OracleComp OracleSpec OracleQuery

-- /-- `OracleInterface` is a type class that provides an oracle interface for a type `Message`.
--   It consists of:
--   - a query type `Domain`,
--   - a response type `Range`,
--   - a function `answer` that given a message `m : Message` and a query `q : Query`,
--   returns a response `r : Range`.

-- TODO: turn `(Query, Range)` into a general `PFunctor` (i.e. `Range : Query → Type`) This
-- allows for better compositionality of `OracleInterface`, including (indexed) sum, instead of
-- requiring indexed family of `OracleInterface`s.

-- However, this won't be possible until `OracleSpec` is changed to be an alias for `PFunctor` -/
-- @[ext]
-- class OracleInterface (Message : Type u) extends
--     OracleSpec where
--   answer : QueryImpl toOracleSpec (ReaderT Message Id)

-- namespace OracleInterface

-- /-- The default instance for `OracleInterface`, where the query is trivial (a `Unit`) and the
--   response returns the data. We do not register this as an instance, instead explicitly calling it
--   where necessary.
-- -/
-- def instDefault {Message : Type u} : OracleInterface Message where
--   Domain := Unit
--   Range _ := Message
--   answer _ := do return (← read)

-- instance {Message : Type u} : Inhabited (OracleInterface Message) :=
--   ⟨instDefault⟩

-- open SimOracle

-- /-- Converts an indexed type family of oracle interfaces into an oracle specification.

-- Notation: `[v]ₒ` for when the oracle interfaces can be inferred, and `[v]ₒ'O` for when the oracle
-- interfaces need to be specified. -/
-- def toOracleSpec' (v : Type v) [O : OracleInterface v] : OracleSpec := O.toOracleSpec

-- @[inherit_doc] notation "[" v "]ₒ" => toOracleSpec' v
-- @[inherit_doc] notation "[" v "]ₒ'" oI:max => toOracleSpec' v (O := oI)

-- /-- Given an underlying data for an indexed type family of oracle interfaces `v`,
--     we can give an implementation of all queries to the interface defined by `v` -/
-- def toOracleImpl (v : Type v) [O : OracleInterface v] :
--     QueryImpl [v]ₒ (ReaderT v Id) :=
--   O.answer

-- /-- Any (dependent) function type has a canonical `OracleInterface` instance,
-- whose `answer` is the function itself. -/
-- @[reducible, inline]
-- instance instDFun {α : Type u} {β : α → Type u} :
--     OracleInterface ((t : α) → β t) where
--   Domain := α
--   Range := β
--   answer t := do return (← read) t

-- instance (v : Type v) [O : OracleInterface v]
--     [h : DecidableEq (O.Domain)] [h' : ∀ t, DecidableEq (O.Range t)] :
--     [v]ₒ.DecidableEq where
--   decidableEq_A := h
--   decidableEq_B := h'

-- instance (v : Type v) [O : OracleInterface v] [h : ∀ t, Fintype (O.Range t)] :
--     [v]ₒ.Fintype where
--   fintype_B := h

-- instance (v : Type v) [O : OracleInterface v] [h : ∀ t, Inhabited (O.Range t)] :
--     [v]ₒ.Inhabited where
--   inhabited_B := h

-- @[reducible, inline] -- dtumad: I'm not sure if this makes sense to have still?
-- instance {ι₁ : Type u} {T₁ : ι₁ → Type v} [inst₁ : ∀ i, OracleInterface (T₁ i)]
--     {ι₂ : Type u} {T₂ : ι₂ → Type v} [inst₂ : ∀ i, OracleInterface (T₂ i)] :
--     ∀ i, OracleInterface (Sum.rec T₁ T₂ i) :=
--   fun i => match i with
--     | .inl i => inst₁ i
--     | .inr i => inst₂ i

-- @[reducible, inline]
-- protected def tensorProd {α β : Type _} (O₁ : OracleInterface α) (O₂ : OracleInterface β) :
--     OracleInterface (α × β) where
--   Domain := O₁.Domain × O₂.Domain
--   Range t := O₁.Range t.1 × O₂.Range t.2
--   answer | (q₁, q₂) => do
--     let (a, b) ← read
--     return ((O₁.answer q₁).run a, (O₂.answer q₂).run b)

-- @[reducible, inline]
-- instance prod {α β : Type _} (O₁ : OracleInterface α) (O₂ : OracleInterface β) :
--     OracleInterface (α × β) where
--   Domain := O₁.Domain ⊕ O₂.Domain
--   Range
--     | .inl t => O₁.Range t
--     | .inr t => O₂.Range t
--   answer
--     | .inl q => do (O₁.answer q).run (← read).1
--     | .inr q => do (O₂.answer q).run (← read).2

-- /-- The tensor product oracle interface for the product of two types `α` and `β`, each with its own
--   oracle interface, is defined as:
--   - The query & response types are the product of the two query & response types.
--   - The oracle will run both oracles and return the pair of responses.

-- This is a low priority instance since we do not expect to have this behavior often. See `instProd`
-- for the sum behavior on the interface. -/
-- @[reducible, inline]
-- instance (priority := low) instTensorProd {α β : Type _}
--     [O₁ : OracleInterface α] [O₂ : OracleInterface β] : OracleInterface (α × β) :=
--   OracleInterface.tensorProd O₁ O₂

-- /-- The product oracle interface for the product of two types `α` and `β`, each with its own oracle
--   interface, is defined as:
--   - The query & response types are the sum type of the two query & response types.
--   - The oracle will answer depending on the input query.

-- This is the behavior more often assumed, i.e. when we send multiple oracle messages in a round.
-- See `instTensor` for the tensor product behavior on the interface. -/
-- @[reducible, inline]
-- instance instProd {α β : Type _}
--     [O₁ : OracleInterface α] [O₂ : OracleInterface β] : OracleInterface (α × β) :=
--   OracleInterface.prod O₁ O₂

-- /-- The indexed tensor product oracle interface for the dependent product of a type family `v`,
--     indexed by `ι`, each having an oracle interface, is defined as:
--   - The query & response types are the dependent product of the query & response types of the type
--     family.
--   - The oracle, on a given query specifying the index `i` of the type family, will run the oracle of
--     `v i` and return the response.

-- This is a low priority instance since we do not expect to have this behavior often. See
-- `instProdForall` for the product behavior on the interface (with dependent sums for the query and
-- response types). -/
-- @[reducible, inline]
-- instance (priority := low) instTensorForall {ι : Type u} (v : ι → Type v)
--     [O : ∀ i, OracleInterface (v i)] : OracleInterface (∀ i, v i) where
--   Domain := (i : ι) → (O i).Domain
--   Range t := (i : ι) → (O i).Range (t i)
--   answer := fun f q i => (O i).answer (f i) (q i)

-- /-- The indexed product oracle interface for the dependent product of a type family `v`, indexed by
--     `ι`, each having an oracle interface, is defined as:
--   - The query & response types are the dependent product of the query & response types of the type
--     family.
--   - The oracle, on a given query specifying the index `i` of the type family, will run the oracle
--     of `v i` and return the response.

-- This is the behavior usually assumed, i.e. when we send multiple oracle messages in a round.
-- See `instTensorForall` for the tensor product behavior on the interface. -/
-- @[reducible, inline]
-- instance instProdForall {ι : Type u} (v : ι → Type v) [O : ∀ i, OracleInterface (v i)] :
--     OracleInterface (∀ i, v i) where
--   Domain := (i : ι) × (O i).Domain
--   Range t := (O t.1).Range t.2
--   answer := fun ⟨i, q⟩ => do return (O i).answer (f i) q

-- -- def append {ι₁ : Type u} {T₁ : ι₁ → Type v} [∀ i, OracleInterface (T₁ i)]
-- --     {ι₂ : Type u} {T₂ : ι₂ → Type v} [∀ i, OracleInterface (T₂ i)] : OracleSpec (ι₁ ⊕ ι₂) :=
-- --   [Sum.rec T₁ T₂]ₒ

-- /-- Combines multiple oracle specifications into a single oracle by routing queries to the
--       appropriate underlying oracle. Takes:
--     - A base oracle specification `oSpec`
--     - An indexed type family `T` with `OracleInterface` instances
--     - Values of that type family
--   Returns a stateless oracle that routes queries to the appropriate underlying oracle. -/
-- def simOracle (oSpec : OracleSpec) {T : Type w}
--     [O : OracleInterface T] (t : T) :
--     QueryImpl (oSpec + [T]ₒ) (OracleComp oSpec)
--   | .inl t => do query t
--   | .inr q => do return (O.answer q).run t

-- /-- Combines multiple oracle specifications into a single oracle by routing queries to the
--       appropriate underlying oracle. Takes:
--     - A base oracle specification `oSpec`
--     - Two indexed type families `T₁` and `T₂` with `OracleInterface` instances
--     - Values of those type families
--   Returns a stateless oracle that routes queries to the appropriate underlying oracle. -/
-- def simOracle2 (oSpec : OracleSpec)
--     {T₁ : Type w} [O₁ : OracleInterface T₁]
--     {T₂ : Type w} [O₂ : OracleInterface T₂]
--     (t₁ : T₁) (t₂ : T₂) : QueryImpl (oSpec + ([T₁]ₒ + [T₂]ₒ)) (OracleComp oSpec)
--   | .inl t => do query t
--   | .inr (.inl q) => do return (O₁.answer q).run t₁
--   | .inr (.inr q) => do return (O₂.answer q).run t₂

open Finset in
/-- A message type together with a `OracleContext` instance is said to have **oracle distance**
  (at most) `d` if for any two distinct messages, there is at most `d` queries that distinguish
  them, i.e.

  `#{t | OracleInterface.answer a t = OracleInterface.answer b t} ≤ d`.

  Importantly, we quantify the number of oracle inputs not the number of `OracleQuery` elements.
  This property corresponds to the distance of a code, when the oracle instance is to encode the
  message and the query is a position of the codeword. In particular, it applies to
  `(Mv)Polynomial`. -/
def OracleContext.distanceLE {ι} (Message : Type*) (O : OracleContext ι (ReaderM Message))
    [Fintype ι] [O.spec.DecidableEq] (d : ℕ) : Prop :=
  ∀ a b : Message, a ≠ b →
    #{t : O.spec.Domain | ((O.impl t).run a).run = ((O.impl t).run b).run} ≤ d

section Polynomial

open Polynomial MvPolynomial

variable {R : Type*} [CommSemiring R] {d : ℕ} {σ : Type*}

/-- Univariate polynomials can be accessed via evaluation queries. -/
@[reducible, inline]
def instPolynomial : OracleContext R (ReaderM R[X]) where
  spec := R →ₒ R
  impl point := do return (← read).eval point

/-- Univariate polynomials with degree at most `d` can be accessed via evaluation queries. -/
@[reducible, inline]
def instPolynomialDegreeLE : OracleContext R (ReaderM R⦃≤ d⦄[X]) where
  spec := R →ₒ R
  impl point := do return (← read).1.eval point

/-- Univariate polynomials with degree less than `d` can be accessed via evaluation queries. -/
@[reducible, inline]
def instPolynomialDegreeLT : OracleContext R (ReaderM R⦃< d⦄[X]) where
  spec := R →ₒ R
  impl point := do return (← read).1.eval point

/-- Multivariate polynomials can be accessed via evaluation queries. -/
@[reducible, inline]
def instMvPolynomial {σ} : OracleContext (σ → R) (ReaderM R[X σ]) where
  spec := (σ → R) →ₒ R
  impl point := do return (← read).eval point

/-- Multivariate polynomials with individual degree at most `d` can be accessed via evaluation
queries. -/
@[reducible, inline]
def instMvPolynomialDegreeLE {σ} : OracleContext (σ → R) (ReaderM R⦃≤ d⦄[X σ]) where
  spec := (σ → R) →ₒ R
  impl point := do return (← read).1.eval point

-- instance {σ} [Fintype σ] [DecidableEq σ] [Fintype R] :
--     Fintype ((@instMvPolynomialDegreeLE R _ d σ).Domain) :=
--   inferInstanceAs (Fintype (σ → R))

end Polynomial

-- section Vector

-- variable {n : ℕ} {α : Type*}

-- /- Vectors of the form `Fin n → α` can be accessed via queries on their indices. We no longer have
--    this instance separately since it can be inferred from the instance for `Function`. -/
-- -- instance instOracleInterfaceForallFin :
-- --     OracleInterface (Fin n → α) := OracleInterface.instFunction

-- /-- Vectors of the form `List.Vector α n` can be accessed via queries on their indices. -/
-- instance instListVector : OracleInterface (List.Vector α n) where
--   Domain := Fin n
--   Range _ := α
--   answer i := do return (← read)[i]

-- /-- Vectors of the form `Vector α n` can be accessed via queries on their indices. -/
-- instance instVector : OracleInterface (Vector α n) where
--   Domain := Fin n
--   Range _ := α
--   answer i := do return (← read)[i]

-- end Vector

-- end OracleInterface

section PolynomialDistance

-- TODO: refactor these theorems and move them into the appropriate `(Mv)Polynomial` files

open Polynomial MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ} [Fintype R] [DecidableEq R] [IsDomain R]

-- TODO: golf this theorem
@[simp]
theorem distanceLE_polynomial_degreeLT :
    instPolynomialDegreeLT.distanceLE (R⦃< d⦄[X]) (d - 1) := by
  stop
  simp [distanceLE, instPolynomialDegreeLT, mem_degreeLT]
  intro p hp p' hp' hNe
  have : ∀ q ∈ Finset.univ, p.eval q = p'.eval q ↔ q ∈ (p - p').roots := by
    intro q _
    simp
    constructor <;> intro h
    · constructor
      · intro h'; contrapose! hNe; exact sub_eq_zero.mp h'
      · simp [h]
    · exact sub_eq_zero.mp h.2
  conv =>
    enter [1, 1]
    apply Finset.filter_congr this
  simp [Membership.mem, Finset.filter, Finset.card]
  have : (p - p').roots.card < d := by
    have hSubNe : p - p' ≠ 0 := sub_ne_zero_of_ne hNe
    have hSubDegLt : (p - p').degree < d := lt_of_le_of_lt (degree_sub_le p p') (by simp [hp, hp'])
    have := Polynomial.card_roots hSubNe
    have : (p - p').roots.card < (d : WithBot ℕ) := lt_of_le_of_lt this hSubDegLt
    simp at this; exact this
  refine Nat.le_sub_one_of_lt (lt_of_le_of_lt ?_ this)
  apply Multiset.card_le_card
  rw [Multiset.le_iff_subset]
  · intro x hx; simp at hx; exact hx
  · simp [Multiset.nodup_iff_count_le_one]
    intro a; simp [Multiset.count_filter, Multiset.count_univ]
    aesop

theorem distanceLE_polynomial_degreeLE :
    instPolynomialDegreeLE.distanceLE (R⦃≤ d⦄[X]) d := by
  stop
  simp [distanceLE, instPolynomialDegreeLE, mem_degreeLE]
  intro a ha b hb hNe
  simp [Finset.card_filter_le_iff]
  intro s hs
  have habNe : a - b ≠ 0 := sub_ne_zero_of_ne hNe
  have hab : (a - b).degree ≤ d := le_trans (degree_sub_le a b) (by simp [ha, hb])
  have : ¬ s.val ≤ (a - b).roots := by
    intro h
    have h1 : s.val.card ≤ (a - b).roots.card := Multiset.card_le_card h
    have h2 : (a - b).roots.card ≤ (d : WithBot ℕ) := le_trans (card_roots habNe) hab
    simp at h2
    contrapose! hs
    exact le_trans h1 h2
  rw [Multiset.le_iff_subset s.nodup] at this
  simp [Multiset.subset_iff] at this
  obtain ⟨x, hMem, hx⟩ := this
  exact ⟨x, hMem, fun h => by simp_all⟩

theorem distanceLE_mvPolynomial_degreeLE {σ : Type _} [Fintype σ] [DecidableEq σ] :
    instMvPolynomialDegreeLE.distanceLE (R⦃≤ d⦄[X σ]) (Fintype.card σ * d) := by
  simp [OracleContext.distanceLE, instMvPolynomialDegreeLE,
    MvPolynomial.mem_restrictDegree]
  intro a ha b hb hNe
  sorry

end PolynomialDistance
