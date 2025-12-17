/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio
import Batteries.Data.Array.Monadic

/-!
  # Helper Definitions and Lemmas to be ported to VCVio
-/

open OracleSpec OracleComp

universe u v

variable {α β γ : Type}

/-- A function that implements the oracle interface specified by `spec`, and queries no further
  oracles.
-/
def OracleSpec.FunctionType {ι} (spec : OracleSpec ι) := (t : spec.Domain) → spec.Range t

namespace OracleSpec

variable {ι} {spec : OracleSpec ι}

-- def QueryLog.getQueriesFromIdx (log : QueryLog spec) (i : ι) :
--     List (spec.Domain i × spec.Range i) :=
--   log i

end OracleSpec

namespace OracleComp

variable {ι} {spec : OracleSpec ι} {α σ : Type}

/-- Run an oracle computation `OracleComp spec α` with an oracle coming from
  a (deterministic) function `f` that queries no further oracles.

  TODO: add state for `f`
-/
@[reducible]
def runWithOracle (f : (t : spec.Domain) → spec.Range t)
    (mx : OracleComp spec α) : Option α :=
  let f' : QueryImpl spec Id := f
  simulateQ f' mx

@[simp]
theorem runWithOracle_pure (f : (t : spec.Domain) → spec.Range t) (a : α) :
    runWithOracle f (pure a) = some a := by
  simp [runWithOracle]
  rfl

@[simp]
theorem runWithOracle_bind (f : (t : spec.Domain) → spec.Range t)
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    runWithOracle f (oa >>= ob) =
    (runWithOracle f oa) >>=
    (fun x => runWithOracle f (ob x)) := by
  simp [runWithOracle]
  rfl

-- Oracle with bounded use; returns `default` if the oracle is used more than `bound` times.
-- We could then have the Range be an `Option` type, so that `default` is `none`.
-- def boundedUseOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} (bound : ι → ℕ) :
--     spec →[ι → ℕ]ₛₒ spec := fun i query queryCount =>
--   if queryCount i > bound i then
--     return ⟨default, queryCount⟩
--   else
--     countingOracle i query queryCount

-- Single use oracle
-- @[reducible]
-- def singleUseOracle {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} :
--     spec →[ι → ℕ]ₛₒ spec :=
--   boundedUseOracle (fun _ ↦ 1)

-- set_option linter.unusedVariables false in
-- /-- `SatisfiesM` for `OracleComp` -/
-- @[simp]
-- theorem SatisfiesM_OracleComp_eq {p : α → Prop} {x : OracleComp spec α} :
--     SatisfiesM (m := OracleComp spec) p x ↔
--       (∀ a, x = liftM (pure a) → p a) ∧
--         (∀ i q oa, x = queryBind' i q _ oa →
--           ∀ a, SatisfiesM (m := OracleComp spec) p (oa a)) where
--   mp h := by
--     obtain ⟨ x', hx' ⟩ := h
--     constructor
--     · intro a h'
--       simp_all
--       match x' with
--       | pure' _ ⟨ _, h'' ⟩ => simp_all; exact hx' ▸ h''
--     · intro i q oa h' a
--       simp_all
--       match x' with
--       | queryBind' i' q' _ oa' =>
--         simp [map_bind] at hx'
--         obtain ⟨ hi, hq, hoa ⟩ := hx'
--         subst hi hoa hq h'
--         refine ⟨ oa' a, by simp ⟩
--   -- For some reason `h` is marked as unused variable
--   -- Probably due to `simp_all`
--   mpr := fun h => match x with
--     | pure' _ a => by
--       simp_all
--       exact ⟨ pure' _ ⟨a , h⟩, by simp ⟩
--     | queryBind' i q _ oa => by
--       simp_all
--       have hBind' := h i q rfl
--       simp at hBind'
--       have h' := fun a => Classical.choose_spec (hBind' a)
--       exact ⟨ queryBind' i q _ (fun a =>Classical.choose (hBind' a)), by simp [map_bind, h'] ⟩
--     | failure' _ => by sorry

/-- True if every non-`none` element of the cache has that same value in the oracle -/
def Oracle.containsCache {spec : OracleSpec ι}
    (f : (t : spec.Domain) → spec.Range t) (cache : spec.QueryCache) :
    Prop :=
  ∀ q r, cache q = some r → f q = r

/-- For any cache, there is a function to contain it -/
lemma Oracle.containsCache_of_cache {spec : OracleSpec ι}
    [spec.Inhabited]
    (cache : spec.QueryCache) :
    ∃ (f : (t : spec.Domain) → spec.Range t), Oracle.containsCache f cache := by
  use fun q =>
    match cache q with
    | none => default
    | some r => r
  unfold Oracle.containsCache
  intro q r h
  cases cache q with
  | none => simp_all
  | some val => simp_all

/--
For a particular cache, the oracle never fails on that cache
iff it never fails when run with any oracle function that is compatible with the cache.
-/
theorem randomOracle_cache_neverFails_iff_runWithOracle_neverFails {β}
    [spec.DecidableEq] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp (spec) β) (preexisting_cache : spec.QueryCache)
    :
    HasEvalSPMF.NeverFail ((simulateQ randomOracle oa).run preexisting_cache)
    ↔
    (∀ (f : (t : spec.Domain) → spec.Range t),
      Oracle.containsCache f preexisting_cache →
      (runWithOracle f oa).isSome) := by
  stop
  haveI : (i : ι) → Inhabited (OracleSpec.Range spec i) := by
    sorry
  -- todo
  -- ((oa.simulateQ randomOracle).run preexisting_cache).neverFails ↔ never fails for any supercache
  induction oa using OracleComp.inductionOn with
  | pure x =>
    simp_all
  | query_bind i t oa ih =>
    simp_all
    set pre := preexisting_cache i t with pre_eq
    clear_value pre
    cases pre with
    | none =>
      simp_all only [StateT.run_bind, StateT.run_monadLift, monadLift_self, bind_pure_comp,
        StateT.run_modifyGet, Functor.map_map, neverFails_map_iff, neverFails_uniformOfFintype,
        support_map, support_uniformOfFintype, Set.image_univ, Set.mem_Range, Prod.mk.injEq,
        exists_eq_left, forall_eq', true_and]
      constructor
      · intro h f hf
        sorry
      · sorry
    | some val => sorry
  | failure =>
    simp_all
    exact Oracle.containsCache_of_cache preexisting_cache

/--
For a particular oracle function, the computation succeeds with that oracle function
iff it succeeds when initialized with a cache that contains all of data from that oracle function.
-/
theorem runWithOracle_succeeds_iff_simulateQ_randomOracle_neverFails
     {β} [spec.DecidableEq] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp (spec) β) (f : (t : spec.Domain) → spec.Range t) :
    (runWithOracle f oa).isSome ↔
    (HasEvalSPMF.NeverFail ((simulateQ randomOracle oa).run (fun q => some (f q)))) := by
  sorry

/--
The oracle never fails on any cache
iff it never fails when run with any oracle function.
-/
theorem randomOracle_neverFails_iff_runWithOracle_neverFails {β}
    [spec.DecidableEq] [(t : spec.Domain) → SampleableType (spec.Range t)]
    (oa : OracleComp (spec) β)
    :
    (∀ (preexisting_cache : spec.QueryCache), HasEvalSPMF.NeverFail
      ((simulateQ randomOracle oa).run preexisting_cache))
    ↔
    (∀ (f : (t : spec.Domain) → spec.Range t),
      (runWithOracle f oa).isSome) := by
  constructor
  · intro h f
    rw [runWithOracle_succeeds_iff_simulateQ_randomOracle_neverFails]
    exact h fun q ↦ some (f q)
  · intro h preexisting_cache
    sorry

end OracleComp

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]
    {m' : Type u → Type v} [Monad m'] [LawfulMonad m']

namespace QueryImpl

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι} [spec.DecidableEq] {m : Type u → Type v}
  [Monad m]

/-- Compose a query implementation from `spec` to some monad `m`, with a further monad homomorphism
  from `m` to `m'`. -/
def composeM {m' : Type u → Type v} [Monad m'] (hom : m →ᵐ m') (so : QueryImpl spec m) :
    QueryImpl spec m' :=
  fun t => hom (so t)

end QueryImpl
