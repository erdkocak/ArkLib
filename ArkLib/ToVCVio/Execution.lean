/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.SimOracle
import ArkLib.ToVCVio.Lemmas
import ArkLib.OracleReduction.Execution
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.SimulateQ
import Mathlib.Data.ENNReal.Basic
import VCVio.OracleComp.DistSemantics.EvalDist
import ArkLib.OracleReduction.OracleInterface
import ArkLib.ToVCVio.StateTLemmas

/-!
## Monad-to-Logic Bridge Lemmas

This file contains lemmas that simplify the execution of *oracle reductions*.
The goal is to provide a **clean path** from `simulateQ` and `StateT`
to the underlying deterministic protocol logic.

### Layer 1: Protocol Unrolling

**Goal:** Strip away the `Fin.induction` and `processRound` abstractions.

Key lemmas:
- `Reduction.run_step`
  Breaks a protocol execution into a sequential `do` block.
- `Prover.run_succ`
  Specifically handles the `Fin.induction` inside the `Prover.run` code.
- `Transcript.equiv_eval`
  Simplifies the conversion between transcripts and individual
  message/challenge pairs.

### Layer 2: Simulation & Query Mapping

**Goal:** Map queries to their implementations and handle spec-lifting.

Key lemmas:
- `simulateQ_liftComp`
  Simplifies simulating a computation lifted from a smaller specification.
- `simulateQ_append_inl` / `simulateQ_append_inr`
  The *workhorse* lemmas that route queries through `impl₁ ++ₛₒ impl₂`.
- `simulateQ_pure_bind`
  Eliminates pure calls inside simulation blocks.

### Layer 3: State & Support Bridge

**Goal:** Connect `ProbComp` support reasoning to logical relations.

Key lemmas:
- `run'_pure_bind`
  Simplifies `(pure x >>= f).run' s` to `(f x).run' s`.
- `support_pure_bind`
  Flattens the support of nested pure operations in the probability space.
- `probEvent_eq_one_pure_iff`
  Converts a probability statement `Pr[P x] = 1` into the logical claim `P x`.

-/

open OracleSpec OracleComp ProtocolSpec Sum

universe u v w

section SimulationLemmas

variable {ι ι₁ ι₂ : Type*} {spec spec₁ spec₂ : OracleSpec ι}
  {m : Type u → Type v} [AlternativeMonad m] [LawfulMonad m] [LawfulAlternative m]
  {α β σ : Type u}

/-- Lift an implementation for `spec₂` to `spec₁` via `MonadLift`. -/
@[reducible]
def QueryImpl.lift {ι₁ ι₂ : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [MonadLift (OracleQuery spec₁) (OracleQuery spec₂)] (so : QueryImpl spec₂ m) :
    QueryImpl spec₁ m where
  impl q := so.impl (liftM q)

/-- If a computation is lifted from a sub-specification, we can commute the
  lifting and the simulation. -/
@[simp]
lemma simulateQ_liftComp {ι₁ ι₂ : Type u} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    [h : MonadLift (OracleQuery spec₁) (OracleQuery spec₂)] (so : QueryImpl spec₂ m)
    (oa : OracleComp spec₁ α) :
    simulateQ so (liftComp oa spec₂) = simulateQ (QueryImpl.lift so) oa :=
by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [QueryImpl.lift, OracleComp.simulateQ_pure]
  | query_bind i t oa ih => simp [ih, Function.comp_def, QueryImpl.lift]
  | failure => simp [QueryImpl.lift]

omit [LawfulAlternative m] in
/-- Distribution of simulation over query implementation appends for left queries. -/
@[simp]
lemma simulateQ_append_inl (so₁ : QueryImpl spec₁ m) (so₂ : QueryImpl spec₂ m)
    (i : ι) (t : spec₁.domain i) :
    simulateQ (so₁ ++ₛₒ so₂) (liftM (query (spec := spec₁ ++ₒ spec₂) (Sum.inl i) t)) = so₁.impl (query i t) :=
by simp only [simulateQ_query]; rfl

omit [LawfulAlternative m] in
/-- Distribution of simulation over query implementation appends for right queries. -/
@[simp]
lemma simulateQ_append_inr (so₁ : QueryImpl spec₁ m) (so₂ : QueryImpl spec₂ m)
    (i : ι) (t : spec₂.domain i) :
    simulateQ (so₁ ++ₛₒ so₂) (liftM (query (spec := spec₁ ++ₒ spec₂) (Sum.inr i) t)) = so₂.impl (query i t) :=
by simp only [simulateQ_query]; rfl

omit [LawfulMonad m] [LawfulAlternative m] in
/-- Removing pure values from simulation binds. -/
@[simp]
lemma simulateQ_pure_bind (so : QueryImpl spec m) (x : α) (f : α → OracleComp spec β) :
    simulateQ so (pure x >>= f) = simulateQ so (f x) :=
by simp only [pure_bind]

omit [LawfulAlternative m] in
/-- Simulating a lifted query resolves to the implementation of the query.
This is an alias for `simulateQ_query` but explicitly for the `liftM` form. -/
@[simp]
lemma simulateQ_liftM (so : QueryImpl spec m) (q : OracleQuery spec α) :
    simulateQ so (liftM q) = so.impl q :=
simulateQ_query so q

end SimulationLemmas

section SafetyPreservation

variable {ι : Type} {spec : OracleSpec ι} [spec.FiniteRange] {α β : Type}

/-- TODO: might not use this
**Step 3 Helper: Convert 'if' Support to Equality**
If a computation is purely an `if/then/else` structure returning `pure` values,
then `x ∈ support` is equivalent to `x = if ... then ... else ...`.

This allows you to switch from "Set Membership" to "Functional Equality"
without manually doing `split_ifs`.
-/
lemma mem_support_if_pure_eq
    {spec : OracleSpec ι} {α : Type u}
    (p : Prop) [Decidable p] (a b x : α) :
    x ∈ (if p then pure a else pure b : OracleComp spec α).support ↔
    x = if p then a else b := by
  -- Split the if and show equality in both branches
  split_ifs with h
  · simp only [h, OracleComp.support_pure, Set.mem_singleton_iff, if_true]
  · simp only [h, OracleComp.support_pure, Set.mem_singleton_iff, if_false]

/-- **Reverse Safety Preservation (Stateless)**

If the simulated computation is safe and the implementation has the **same support**
as the specification, then the original specification computation is safe.

**Why equality is required**: This lemma proves the reverse direction (simulateQ safe → spec safe).
When we have `x ∈ (liftM q).support` from the spec, we need to show `x ∈ (so.impl q).support`
for the implementation. This requires the reverse inclusion, hence we need equality.

**Note**: For the forward direction (spec safe → simulateQ safe), subset is sufficient.
See `simulateQ_preserves_safety` and `simulateQ_preserves_safety_stateful` which only
require `(so.impl q).support ⊆ (liftM q).support`. -/
lemma neverFails_of_simulateQ (so : QueryImpl spec ProbComp)
    (oa : OracleComp spec α)
    (h_supp : ∀ {β} (q : OracleQuery spec β),
      (so.impl q).support = (liftM q : OracleComp spec β).support)
    (h : [⊥|simulateQ so oa] = 0) : [⊥ | oa] = 0 := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind i t oa ih =>
    rw [simulateQ_query_bind] at h
    rw [probFailure_bind_eq_zero_iff] at h
    simp only [probFailure_bind_eq_zero_iff]
    constructor
    · simp only [probFailure_liftM]
    · intro x hx
      -- h.2 : ∀ x ∈ (so.impl (query i t)).support, [⊥ | (simulateQ so ∘ oa) x] = 0
      -- We have hx : x ∈ (liftM (query i t)).support
      -- By h_supp, these supports are equal
      have hx_sim : x ∈ (so.impl (query i t)).support := by rwa [h_supp]
      exact ih x (h.2 x hx_sim)
  | failure => simp at h

/-- **Generic Safety Preservation Lemma for Stateful Implementations**

If an oracle implementation is safe and support-faithful, then simulation preserves safety
from the specification level to the implementation level.

This is a key building block for completeness proofs: it shows that if the spec says
"this computation never fails" and the implementation only returns valid values
(support-faithful), then running the simulated implementation also never fails.

**Parameters:**
- `impl`: The stateful oracle implementation
- `hImplSafe`: Each query implementation is safe (never fails)
- `hImplSupp`: The implementation is support-faithful (only returns valid values)
- `oa`: The oracle computation at the spec level
- `s`: The current state
- `h_oa`: The spec computation is safe

**Conclusion:** The simulated computation is also safe. -/
theorem simulateQ_preserves_safety_stateful
    {oSpec : OracleSpec ι} [oSpec.FiniteRange] {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSafe : ∀ {β} (q : OracleQuery oSpec β) s, [⊥|(impl.impl q).run s] = 0)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support ⊆ (q : OracleComp oSpec β).support)
    {α : Type} (oa : OracleComp oSpec α) (s : σ)
    (h_oa : [⊥|oa] = 0) :
    [⊥|(simulateQ impl oa).run s] = 0 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | failure => simp at h_oa
  | query_bind i t oa ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, probFailure_bind_eq_zero_iff]
    constructor
    · exact hImplSafe (query i t) s
    · intro ⟨result, newState⟩ h_in_supp
      rw [probFailure_bind_eq_zero_iff] at h_oa
      have h_result_in_spec : result ∈ ((query i t) : OracleComp oSpec _).support := by
        apply hImplSupp (query i t) s
        exact Set.mem_image_of_mem Prod.fst h_in_supp
      simp only [OracleComp.support_query, Set.mem_univ] at h_result_in_spec
      have h_result_in_query : result ∈ (query i t : OracleComp oSpec _).support := by
        simp only [OracleComp.support_query, Set.mem_univ]
      exact ih result newState (h_oa.2 result h_result_in_query)

/-- **Reverse Safety Preservation for Stateful Implementations**

If the simulated stateful computation is safe and the implementation has the same support
as the specification, then the original specification computation is safe.

This is the reverse direction of `simulateQ_preserves_safety_stateful`.

**Note**: This requires support **equality** rather than just subset (⊆) because we need
to extract witnesses: if a result is valid in the spec, we need to know that the implementation
can actually produce it (surjectivity).
-/
lemma neverFails_of_simulateQ_stateful
    {oSpec : OracleSpec ι} [oSpec.FiniteRange] {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support = (liftM q : OracleComp oSpec β).support)
    {α : Type} (oa : OracleComp oSpec α) (s : σ)
    (h : [⊥|(simulateQ impl oa).run s] = 0) :
    [⊥|oa] = 0 := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp
  | failure => simp at h
  | query_bind i t oa ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, probFailure_bind_eq_zero_iff] at h
    simp only [probFailure_bind_eq_zero_iff]
    constructor
    · simp only [probFailure_liftM]
    · intro result h_result_in_spec
      -- h.2 : ∀ ⟨result, newState⟩ ∈ ((impl.impl (query i t)).run s).support,
      --       [⊥|(simulateQ impl (oa result)).run newState] = 0
      -- We need to show: [⊥|oa result] = 0
      simp only [OracleComp.support_query, Set.mem_univ] at h_result_in_spec
      -- By support equality, result is in the image of Prod.fst over impl's support
      have h_result_in_impl : result ∈ Prod.fst <$> ((impl.impl (query i t)).run s).support := by
        rw [hImplSupp]
        simp only [OracleComp.support_query, Set.mem_univ]
      -- Extract a witness: there exists a newState such that (result, newState) is in support
      obtain ⟨pair, h_in_supp, h_fst_eq⟩ := h_result_in_impl
      cases pair with | mk result' newState =>
      subst h_fst_eq
      exact ih result' newState (h.2 ⟨result', newState⟩ h_in_supp)

/-- **Stateful Safety Biconditional**

For stateful oracle implementations, the simulated computation is safe if and only if
the specification computation is safe. This requires:
1. The implementation itself never fails (hImplSafe).
2. The implementation has the same support as the specification (hImplSupp).

This is the stateful version of `probFailure_simulateQ_iff` and is useful for
simplifying completeness proofs where you need to establish equivalence between
simulated and specification safety.

**Note**: Unlike `simulateQ_preserves_safety_stateful` which only requires support subset (⊆),
this biconditional requires support **equality** (=) to enable the reverse direction.
-/
theorem probFailure_simulateQ_iff_stateful
    {oSpec : OracleSpec ι} [oSpec.FiniteRange] {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSafe : ∀ {β} (q : OracleQuery oSpec β) s, [⊥|(impl.impl q).run s] = 0)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support = (liftM q : OracleComp oSpec β).support)
    {α : Type} (oa : OracleComp oSpec α) (s : σ) :
    [⊥|(simulateQ impl oa).run s] = 0 ↔ [⊥|oa] = 0 := by
  constructor
  · intro h; exact neverFails_of_simulateQ_stateful impl hImplSupp oa s h
  · intro h
    apply simulateQ_preserves_safety_stateful impl hImplSafe _ oa s h
    intro β q s'
    rw [hImplSupp]

/-- **Stateful Safety Biconditional (run' version)**

This is the `run'` version of `probFailure_simulateQ_iff_stateful`. It works with
`StateT.run'` which projects out only the result (discarding the final state),
rather than `StateT.run` which returns the full `(result, state)` pair.

This lemma is useful when the goal involves `(simulateQ impl oa).run' s` instead of
`(simulateQ impl oa).run s`.
-/
theorem probFailure_simulateQ_iff_stateful_run'
    {oSpec : OracleSpec ι} [oSpec.FiniteRange] {σ : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSafe : ∀ {β} (q : OracleQuery oSpec β) s, [⊥|(impl.impl q).run s] = 0)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support = (liftM q : OracleComp oSpec β).support)
    {α : Type} (oa : OracleComp oSpec α) (s : σ) :
    [⊥|(simulateQ impl oa).run' s] = 0 ↔ [⊥|oa] = 0 := by
  simp only [StateT.run', probFailure_map]
  exact probFailure_simulateQ_iff_stateful impl hImplSafe hImplSupp oa s

/-- **Safety Preservation Lemma for Stateless Implementations**

If an oracle implementation is safe and support-faithful, then simulation preserves safety
from the specification level to the implementation level (stateless version).

This is the stateless counterpart to `simulateQ_preserves_safety_stateful`.
-/
theorem simulateQ_preserves_safety
    {oSpec : OracleSpec ι} [oSpec.FiniteRange]
    (so : QueryImpl oSpec ProbComp)
    (h_so : ∀ {β} (q : OracleQuery oSpec β), [⊥|so.impl q] = 0)
    (h_supp : ∀ {β} (q : OracleQuery oSpec β),
      (so.impl q).support ⊆ (liftM q : OracleComp oSpec β).support)
    {α : Type} (oa : OracleComp oSpec α)
    (h_oa : [⊥|oa] = 0) :
    [⊥|simulateQ so oa] = 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | failure => simp at h_oa
  | query_bind i t oa ih =>
    simp only [simulateQ_query_bind, probFailure_bind_eq_zero_iff]
    constructor
    · exact h_so (query i t)
    · intro result h_in_supp
      rw [probFailure_bind_eq_zero_iff] at h_oa
      have h_result_in_spec : result ∈ (query i t : OracleComp oSpec _).support := by
        exact h_supp (query i t) h_in_supp
      exact ih result (h_oa.2 result h_result_in_spec)

/--
Safety preservation: A simulated protocol is safe if and only if the original
protocol is safe. This requires:
1. The implementation itself never fails (h_so).
2. The implementation doesn't return "illegal" values outside the spec (h_supp).
-/
@[simp]
lemma probFailure_simulateQ_iff (so : QueryImpl spec ProbComp) (oa : OracleComp spec α)
    (h_so : ∀ {β} (q : OracleQuery spec β), [⊥|so.impl q] = 0)
    (h_supp : ∀ {β} (q : OracleQuery spec β),
      (so.impl q).support = (liftM q : OracleComp spec β).support) :
    [⊥|simulateQ so oa] = 0 ↔ [⊥|oa] = 0 := by
  constructor
  · intro h; exact neverFails_of_simulateQ so oa h_supp h
  · intro h_oa
    apply simulateQ_preserves_safety so h_so (h_supp := fun q ↦ (h_supp q).subset) oa h_oa

@[simp]
lemma probFailure_simulateQ_of_probFailure (so : QueryImpl spec ProbComp) (oa : OracleComp spec α)
    (h_so : ∀ {β} (q : OracleQuery spec β), [⊥|so.impl q] = 0)
    (h_supp : ∀ {β} (q : OracleQuery spec β),
      (so.impl q).support ⊆ (liftM q : OracleComp spec β).support) (h_oa : [⊥|oa] = 0) :
    [⊥|simulateQ so oa] = 0 := by
  apply simulateQ_preserves_safety so
  · exact h_so
  · exact h_supp
  · exact h_oa

omit [spec.FiniteRange] in
/-- Spec-lifting preserves the failure probability. -/
@[simp]
lemma probFailure_liftComp_eq {ι' : Type} {superSpec : OracleSpec ι'}
    [spec.FiniteRange] [superSpec.FiniteRange]
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) : [⊥ | liftComp oa superSpec] = [⊥ | oa] := by
  simp only [OracleComp.probFailure_def, OracleComp.evalDist_liftComp]

/-- Challenge query implementations have the same support as the specification.
    This is trivially true for uniform distributions. -/
@[simp]
lemma support_challengeQueryImpl_eq {n : ℕ} {pSpec : ProtocolSpec n}
    [∀ i, SelectableType (pSpec.Challenge i)] (i : pSpec.ChallengeIdx) :
    (challengeQueryImpl.impl (query i ())).support =
    (liftM (query i ()) : OracleComp ([pSpec.Challenge]ₒ'challengeOracleInterface) _).support := by
  -- Both uniformOfFintype and liftM have full support over pSpec.Challenge i
  -- This should be provable using support_uniformOfFintype and support lemmas for liftM
-- 1. Expand the implementation of challengeQueryImpl
  unfold challengeQueryImpl
  -- 2. Simplify the implementation call
  -- 'challengeQueryImpl' is defined as mapping index 'i' to 'uniformOfFintype'
  simp only [ChallengeIdx, Challenge, support_query]
  -- ⊢ support ($ᵗpSpec.Type ↑i) = Set.univ
  rw [OracleComp.support_uniformOfFintype (α := pSpec.Type ↑i)]

/-- Challenge query implementations never fail (stateful version).
    Uniform sampling is always safe regardless of state. -/
@[simp]
lemma probFailure_challengeQueryImpl_run {n : ℕ} {pSpec : ProtocolSpec n} {σ : Type}
    [∀ i, SelectableType (pSpec.Challenge i)]
    (q : ([pSpec.Challenge]ₒ'challengeOracleInterface).OracleQuery β) (s : σ) :
    [⊥|(liftM (challengeQueryImpl.impl q) : StateT σ ProbComp β).run s] = 0 := by
  cases q with | query i t =>
  cases t  -- t : Unit, so this eliminates the match
  unfold challengeQueryImpl
  simp only [StateT.run_liftM_lib, probFailure_bind_eq_zero_iff, probFailure_pure]
  -- now apply `probFailure_uniformOfFintype` for the form `[⊥|$ᵗα] = 0`
  exact ⟨@probFailure_uniformOfFintype (α := pSpec.Challenge i) _, fun _ _ => trivial⟩

/-- Challenge query implementations have full support (stateful version).
    The first component of the result has the same support as the spec. -/
@[simp]
lemma support_challengeQueryImpl_run_eq {n : ℕ} {pSpec : ProtocolSpec n} {σ : Type}
    [∀ i, SelectableType (pSpec.Challenge i)]
    (q : ([pSpec.Challenge]ₒ'challengeOracleInterface).OracleQuery β) (s : σ) :
    Prod.fst <$> ((liftM (challengeQueryImpl.impl q) : StateT σ ProbComp β).run s).support =
    (liftM q : OracleComp ([pSpec.Challenge]ₒ'challengeOracleInterface) β).support := by
  cases q with | query i t =>
  cases t  -- t : Unit, eliminate the match
  simp only [StateT.run_liftM_lib, support_bind, support_pure, liftM, support_query]
  ext x
  simp only [ChallengeIdx, support_challengeQueryImpl_eq, support_query, Set.mem_univ,
    Set.iUnion_true, Set.iUnion_singleton_eq_range, Set.fmap_eq_image, Set.mem_image, Set.mem_range,
    exists_exists_eq_and, exists_eq]

variable {oSpec : OracleSpec ι}
/--
If the stateful implementation `impl` is support-faithful, then any value
returned during a stateful run is within the support of the original specification.
-/
lemma support_run_subset_support_spec {σ α : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))
    (q : OracleQuery oSpec α) (s : σ)
    (h_faithful : ∀ (s : σ), (Prod.fst <$> (impl.impl q).run s).support ⊆
      (liftM q : OracleComp oSpec α).support) :
    ∀ x' ∈ (Prod.fst <$> (impl.impl q).run s).support,
      x' ∈ (liftM q : OracleComp oSpec α).support :=
by
  intro x' hx'
  exact h_faithful s hx'

end SafetyPreservation

section StateExecutionLemmas

variable {σ α β : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]

/-- Simplify a bind following a pure initialization of state. -/
@[simp]
theorem run'_bind_pure {s : σ} (x : α) (f : α → StateT σ m β) :
    (StateT.run' (pure x >>= f) s) = (StateT.run' (f x) s) :=
by simp [StateT.run']

alias run'_pure_bind := run'_bind_pure

/-- Bridge between monadic support and deterministic results for pure ProbComp. -/
@[simp]
lemma support_pure_bind_pure {α β : Type} (x : α) (f : α → ProbComp β) :
    (pure x >>= f).support = (f x).support :=
by simp

alias support_pure_bind := support_pure_bind_pure

end StateExecutionLemmas

section ProtocolUnrolling

variable {ι : Type} {n : ℕ} {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}

/-- Unrolls one round of the prover's induction for a P -> V step. -/
@[simp]
lemma Prover_processRound_P_to_V (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (j : Fin n) (transcript : pSpec.Transcript j.castSucc) (state : prover.PrvState j.castSucc)
    (h : pSpec.dir j = .P_to_V) :
    prover.processRound j (pure (transcript, state)) =
      (do
        let ⟨msg, state'⟩ ← prover.sendMessage ⟨j, h⟩ state
        return (transcript.concat msg, state')) :=
by
  rw [Prover.processRound]
  simp only [bind_pure_comp, pure_bind]
  split <;> rename_i h_dir
  · rw [h] at h_dir; contradiction
  · simp_all

/-- Unrolls one round of the prover's induction for a V -> P step. -/
@[simp]
lemma Prover_processRound_V_to_P (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (j : Fin n) (transcript : pSpec.Transcript j.castSucc) (state : prover.PrvState j.castSucc)
    (h : pSpec.dir j = .V_to_P) :
    prover.processRound j (pure (transcript, state)) =
      (do
        let challenge ← pSpec.getChallenge ⟨j, h⟩
        letI newState := (← prover.receiveChallenge ⟨j, h⟩ state) challenge
        return (transcript.concat challenge, newState)) :=
by
  rw [Prover.processRound]
  simp only [bind_pure_comp, pure_bind]
  split <;> rename_i h_dir
  · simp_all
  · rw [h] at h_dir; contradiction

/-- Simplifies the probability event of a deterministic pure result. -/
@[simp]
lemma probEvent_pure_iff {α : Type} [DecidableEq α] (p : α → Prop) [DecidablePred p] (x : α) :
    [p | (pure x : ProbComp α)] = 1 ↔ p x :=
by
  simp only [probEvent_pure, ite_eq_left_iff]
  exact ⟨fun h => by simpa using h, fun h => by simp [h]⟩

alias probEvent_eq_one_pure_iff := probEvent_pure_iff

end ProtocolUnrolling

section ReductionUnrolling

variable {ι : Type} {n : ℕ} {pSpec : ProtocolSpec n} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [∀ i, SelectableType (pSpec.Challenge i)]

omit [(i : pSpec.ChallengeIdx) → SelectableType (pSpec.Challenge i)] in
/-- Unrolls the initial step of the Prover's induction. -/
@[simp]
lemma Prover_run_induction_zero (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (input : StmtIn × WitIn) :
    prover.runToRound 0 input.1 input.2 =
      Pure.pure (default, prover.input input) :=
by simp [Prover.runToRound]

omit [(i : pSpec.ChallengeIdx) → SelectableType (pSpec.Challenge i)] in
/-- Specifically handles the `Fin.induction` inside the `Prover.run` code. -/
@[simp]
lemma Prover.run_succ (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn) (i : Fin n) :
    prover.runToRound i.succ stmt wit =
      prover.processRound i (prover.runToRound i.castSucc stmt wit) :=
by simp [Prover.runToRound, Fin.induction_succ]

omit [(i : pSpec.ChallengeIdx) → SelectableType (pSpec.Challenge i)] in
/-- Simplifies `Reduction.run` by unfolding it into the prover's run and verifier's check. -/
lemma Reduction_run_def (reduction : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmtIn : StmtIn) (witIn : WitIn) :
    reduction.run stmtIn witIn = (do
      let ⟨transcript, stmtOut, witOut⟩ ← reduction.prover.run stmtIn witIn
      let verifierStmtOut ← reduction.verifier.verify stmtIn transcript
      return ((transcript, stmtOut, witOut), verifierStmtOut)) :=
by rfl

alias Reduction.run_step := Reduction_run_def

/-- Core Lemma: If the prover and verifier are simulated, the challenge query
    maps directly to the challenge index in the transcript. -/
@[simp]
lemma simulateQ_getChallenge (j : Fin n) (h : pSpec.dir j = .V_to_P)
    (so : QueryImpl oSpec ProbComp) :
    simulateQ (so ++ₛₒ challengeQueryImpl)
      (liftComp (pSpec.getChallenge ⟨j, h⟩) (oSpec ++ₒ [pSpec.Challenge]ₒ)) =
      uniformOfFintype (pSpec.Challenge ⟨j, h⟩) :=
by
  unfold getChallenge
  simp only [simulateQ_liftComp, simulateQ_query]
  rfl

end ReductionUnrolling

section TranscriptLemmas

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- Simplifies the extraction of a message from a full transcript. -/
@[simp]
lemma Transcript_get_message (tr : pSpec.FullTranscript) (j : Fin n) (h : pSpec.dir j = .P_to_V) :
    tr.messages ⟨j, h⟩ = tr j :=
by rfl

/-- Simplifies the extraction of a challenge from a full transcript. -/
@[simp]
lemma Transcript_get_challenge (tr : pSpec.FullTranscript) (j : Fin n) (h : pSpec.dir j = .V_to_P) :
    tr.challenges ⟨j, h⟩ = tr j :=
by rfl

/-- Simplifies the conversion between transcripts and individual message/challenge pairs. -/
lemma Transcript.equiv_eval (tr : pSpec.FullTranscript) :
    FullTranscript.equivMessagesChallenges tr = (tr.messages, tr.challenges) :=
by rfl

end TranscriptLemmas

section SafetyLemmas

variable {ι : Type} {spec : OracleSpec ι} [spec.FiniteRange] {α β : Type}
  {m : Type → Type} [AlternativeMonad m] [LawfulAlternative m]

omit [spec.FiniteRange] in
/-- The support of a lifted computation is the same as the original. -/
@[simp]
lemma support_liftComp {ι' : Type} {superSpec : OracleSpec ι'}
    [MonadLift (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) : (liftComp oa superSpec).support = oa.support := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind i t oa ih => simp [ih]
  | failure => simp

omit [spec.FiniteRange] in
@[simp]
lemma support_simulateQ_eq (so : QueryImpl spec ProbComp) (oa : OracleComp spec α)
    (h_supp : ∀ {β} (q : OracleQuery spec β),
      (so.impl q).support = (liftM q : OracleComp spec β).support) :
    (simulateQ so oa).support = oa.support := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind i t oa ih =>
    simp [simulateQ_bind, ih, h_supp]
  | failure => simp

omit [spec.FiniteRange] in
/-- **Support Preservation Lemma for Stateless Implementations**

If each query implementation's support is a subset of the spec's support,
then the support of the simulated computation is a subset of the original.

**Meaning**:
This lemma establishes that simulation does not introduce new possible outcomes
beyond what the original specification allowed, provided the query-level
implementation is faithful to the specification's possible results.

**Application**:
- **Safety Proofs / Perfect Completeness**: This is the primary tool for reasoning
  about `perfectCompleteness`. To show `[⊥|simulateQ so oa] = 0`, we only need
  to know that the implementation's support is a subset of the spec's support
  (and that the implementation itself never fails). It is **not** an `iff`
  because an implementation can be safer or more restrictive than its
  specification (e.g., a deterministic implementation of a random oracle).
- **Deterministic Implementations**: Crucial for cases where an oracle is
  implemented deterministically (singleton support), which is naturally a subset
  of a more general specification (e.g., `Set.univ`).
- **Refining Results**: Allows lifting properties proven about the high-level
  `oa.support` to the concrete simulated implementation.

**Note on Equality (`=`) vs Subset (`⊆`)**:
While we also have `support_simulateQ_eq` for cases where support is exactly
preserved, security reasoning for completeness rarely requires equality. Subset
is more flexible as it allows "fixing" oracle randomness to a single value
(common in transcript-based reductions) without breaking the proof.
-/
lemma support_simulateQ_subset (so : QueryImpl spec ProbComp) (oa : OracleComp spec α)
    (h_supp : ∀ {β} (q : OracleQuery spec β),
      (so.impl q).support ⊆ (liftM q : OracleComp spec β).support) :
    (simulateQ so oa).support ⊆ oa.support := by
  induction oa using OracleComp.induction with
  | pure a => simp
  | query_bind i t ou ih =>
    simp only [simulateQ_query_bind, support_bind]
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨y, hy_so, hx_sim⟩ := hx
    exact ⟨y, h_supp (query i t) hy_so, ih y hx_sim⟩
  | failure => simp

/-- **Helper: Support of run' for stateful simulateQ**

If a stateful oracle implementation is support-faithful, then for any state `s`,
the support of `(simulateQ impl oa).run' s` equals the support of `oa`.

This is the stateful version of `support_simulateQ_eq` and is used as a building
block for `support_bind_simulateQ_run'_eq`.

**Proof Strategy**: The proof requires careful handling of state transitions.
The key insight is that `run'` projects out the result component via `map Prod.fst`,
and `hImplSupp` ensures that the first component of the stateful implementation's
support matches the spec's support. The proof proceeds by induction on `oa`,
using the support-faithfulness at each query step.
-/
lemma support_simulateQ_run'_eq
    {oSpec : OracleSpec ι} [oSpec.FiniteRange] {σ α : Type}
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec α) (s : σ)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support = (liftM q : OracleComp oSpec β).support) :
    ((simulateQ impl oa).run' s).support = oa.support := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x =>
    simp only [simulateQ_pure, StateT.run'_pure_lib, support_pure]
  | failure =>
    simp only [simulateQ_failure, StateT.run', support_map, support_failure, Set.image_eq_empty]
    rfl
  | query_bind i t oa ih =>
    simp only [simulateQ_query_bind, StateT.run'_bind_lib, support_bind]
    ext y
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro ⟨⟨x, s'⟩, h_pair, h_y⟩
      have h_x_spec : x ∈ (query i t : OracleComp oSpec _).support := by
        have h_supp_eq := hImplSupp (query i t) s
        rw [← h_supp_eq]
        exact Set.mem_image_of_mem Prod.fst h_pair
      have h_y_spec : y ∈ (oa x).support := by
        rw [← ih x s']
        exact h_y
      exact ⟨x, h_x_spec, h_y_spec⟩
    · intro ⟨x, h_x_spec, h_y_spec⟩
      have h_supp_eq := hImplSupp (query i t) s
      have h_x_in_image : x ∈ Prod.fst <$> ((impl.impl (query i t)).run s).support := by
        rw [h_supp_eq]
        exact h_x_spec
      simp only [Set.fmap_eq_image, Set.mem_image] at h_x_in_image
      obtain ⟨pair, h_pair, h_fst_eq⟩ := h_x_in_image
      cases pair with | mk x' s' =>
      have h_x'_eq_x : x' = x := h_fst_eq
      have h_y_sim : y ∈ ((simulateQ impl (oa x')).run' s').support := by
        rw [ih x' s']
        rw [h_x'_eq_x]
        exact h_y_spec
      have h_y_sim' : y ∈ support (((simulateQ impl ∘ oa) x').run' s') := by
        simp only [Function.comp_apply]
        exact h_y_sim
      exact ⟨(x', s'), h_pair, h_y_sim'⟩

/-- **Support Nonemptiness from Never-Fails**

If a computation never fails, then its support is nonempty. This is a fundamental
property: if `[⊥|oa] = 0`, then there must be at least one possible output value.

**Intuition**: If a computation never fails, the sum of probabilities over all outputs
equals 1. Since probabilities are non-negative and sum to 1, at least one output
must have positive probability, which means it's in the support.

**Application**: This lemma is useful in completeness proofs where we need to eliminate
quantifiers over support. If we have `∀ x ∈ oa.support, P x` and `oa.neverFails`,
we can instantiate the quantifier with a witness from the nonempty support.
-/
theorem support_nonempty_of_neverFails
    {ι : Type} {spec : OracleSpec ι} [spec.FiniteRange] {α : Type}
    (oa : OracleComp spec α) (h : oa.neverFails) :
    oa.support.Nonempty := by
  -- Convert neverFails to probFailure = 0
  have h_probFailure_eq_zero : [⊥|oa] = 0 := by
    rw [probFailure_eq_zero_iff]; exact h
  -- If probFailure = 0, then the sum of probOutput over all outputs is 1
  have h_sum_eq_one : ∑' x : α, [= x | oa] = 1 := by
    rw [tsum_probOutput_eq_sub, h_probFailure_eq_zero, tsub_zero]
  -- If the tsum is 1, then probEvent for True is positive
  have h_event_pos : 0 < [fun _ => True | oa] := by
    -- probEvent for True equals the tsum of probOutput
    rw [OracleComp.probEvent_eq_tsum_ite (p := fun _ => True)]
    -- Simplify: if True then [=x|oa] else 0 = [=x|oa]
    simp only [if_true]
    rw [h_sum_eq_one]
    -- The tsum is 1, which is positive
    norm_num
  -- Use probEvent_pos_iff to get that there exists x in support
  rw [probEvent_pos_iff] at h_event_pos
  obtain ⟨x, hx_mem, _⟩ := h_event_pos
  exact ⟨x, hx_mem⟩

/-- **Support Preservation for Stateful Bind-SimulateQ Pattern**

If a stateful oracle implementation is support-faithful, then the support of
`(do let s ← init; (simulateQ impl oa).run' s)` equals the support of `oa`.

This is the stateful bind version of `support_simulateQ_eq` and is essential
for reasoning about support in oracle reductions where:
- `init : ProbComp σ` samples the initial oracle state
- `impl : QueryImpl oSpec (StateT σ ProbComp)` is a stateful oracle implementation
- `oa : OracleComp oSpec α` is the specification computation (which doesn't depend on state)

**Pattern**: This lemma handles the common pattern in completeness proofs:
```lean
(do let s ← init; (simulateQ impl oa).run' s).support = oa.support
```

**Application**: When proving completeness, we often need to show that the support
of the simulated execution matches the support of the specification. This lemma
bridges that gap for stateful implementations.

**Note**: The RHS is just `oa.support` (not bound with `init`) because `oa` is
a pure specification computation that doesn't depend on the oracle state.
-/
lemma support_bind_simulateQ_run'_eq
    {oSpec : OracleSpec ι} [oSpec.FiniteRange] {σ α : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (oa : OracleComp oSpec α)
    (hInit : init.neverFails)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> ((impl.impl q).run s).support = (liftM q : OracleComp oSpec β).support) :
    (do let s ← init; (simulateQ impl oa).run' s).support = oa.support := by
  -- Expand the bind structure
  simp only [support_bind]
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · -- Forward direction: simulated support ⊆ spec support
    intro ⟨s, hs_init, hx_sim⟩
    -- Use the helper lemma
    have h_supp_eq := support_simulateQ_run'_eq impl oa s hImplSupp
    rw [h_supp_eq] at hx_sim
    exact hx_sim
  · -- Backward direction: spec support ⊆ simulated support
    intro hx_spec
    -- We need to show there exists s ∈ init.support such that x ∈ (simulateQ impl oa).run' s).support
    -- Since init.neverFails (or we can use init.support.Nonempty), we can pick any s
    -- Use the helper lemma
    have h_init_nonempty : init.support.Nonempty :=
      support_nonempty_of_neverFails init hInit
    obtain ⟨s, hs_init⟩ := h_init_nonempty
    have h_supp_eq := support_simulateQ_run'_eq impl oa s hImplSupp
    -- h_supp_eq: ((simulateQ impl oa).run' s).support = oa.support
    -- We have hx_spec: x ∈ oa.support
    -- Need: x ∈ ((simulateQ impl oa).run' s).support
    rw [← h_supp_eq] at hx_spec
    exact ⟨s, hs_init, hx_spec⟩

end SafetyLemmas

section SimOracleSafety
open OracleInterface OracleComp OracleSpec OracleQuery SimOracle

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.FiniteRange]
  {ι₁ : Type} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
  {ι₂ : Type} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]

/-- simOracle2 is safe because it is a deterministic transcript lookup. -/
@[simp]
lemma probFailure_simOracle2 (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) :
    ∀ {β} (q : (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)).OracleQuery β),
    [⊥ | (simOracle2 oSpec t₁ t₂).impl q] = 0 := by
  intro β q
  rw [probFailure_eq_zero_iff]
  exact neverFails_simOracle2 oSpec t₁ t₂ q

/--
**Generic Safety Preservation for simOracle2**

If the underlying computation `oa` is safe (never fails), then simulating it
using `simOracle2` (which uses deterministic transcripts) is also safe.

This lemma handles the administrative proof obligations (implementation safety
and support subset), allowing you to reduce the goal directly to `[⊥|oa] = 0`.
-/
lemma probFailure_simulateQ_simOracle2_eq_zero
    [OracleSpec.FiniteRange [T₁]ₒ] [OracleSpec.FiniteRange [T₂]ₒ]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    {α : Type} (oa : OracleComp (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)) α)
    (h_oa : [⊥|oa] = 0) :
    [⊥ | simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂) oa] = 0 := by
  -- simOracle2 returns QueryImpl spec (OracleComp specₜ), which is Stateless
  -- We prove this directly by induction, following the pattern of simulateQ_preserves_safety
  let so := OracleInterface.simOracle2 oSpec t₁ t₂
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | failure => simp at h_oa
  | query_bind i t oa ih =>
    simp only [simulateQ_query_bind, probFailure_bind_eq_zero_iff]
    constructor
    · -- The oracle implementation never fails
      exact probFailure_simOracle2 t₁ t₂ (query i t)
    · -- For each result in the support, the continuation is safe
      intro result h_in_supp
      rw [probFailure_bind_eq_zero_iff] at h_oa
      -- Show that result is in the spec support
      -- simOracle2: base queries pass through (idOracle), transcript queries return pure values
      have h_result_in_spec : result ∈
        (query i t : OracleComp (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)) _).support := by
        cases i with
        | inl i_base =>
          -- Base queries: idOracle passes through, support is full range
          simp only [OracleComp.support_query, Set.mem_univ]
        | inr i_ext =>
          cases i_ext with
          | inl i_t1 =>
            -- T1 queries: fnOracle returns pure (answer (t₁ i_t1) t)
            -- The support is a singleton, and answer returns a value in the oracle range
            have h_supp : (so.impl (query (.inr (.inl i_t1)) t)).support
              = {OracleInterface.answer (t₁ i_t1) t} := by rfl
            have : result = OracleInterface.answer (t₁ i_t1) t := by
              rwa [h_supp, Set.mem_singleton_iff] at h_in_supp
            rw [this]
            simp only [OracleComp.support_query, Set.mem_univ]
          | inr i_t2 =>
            -- T2 queries: fnOracle returns pure (answer (t₂ i_t2) t)
            have h_supp : (so.impl (query (.inr (.inr i_t2)) t)).support
              = {OracleInterface.answer (t₂ i_t2) t} := by rfl
            have : result = OracleInterface.answer (t₂ i_t2) t := by
              rwa [h_supp, Set.mem_singleton_iff] at h_in_supp
            rw [this]
            -- answer (t₂ i_t2) t is in the range of the oracle for (.inr (.inr i_t2))
            simp only [OracleComp.support_query, Set.mem_univ]
      exact ih result (h_oa.2 result h_result_in_spec)

/--
**SimOracle2 Bind Distribution**

Distributes `simulateQ (simOracle2 ...)` over bind operations, allowing the simplifier
to push simulation through `do` blocks and simplify each component separately.
-/
@[simp]
lemma simulateQ_simOracle2_bind (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    {α β : Type} (oa : OracleComp (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)) α)
    (f : α → OracleComp (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)) β) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂) (oa >>= f) =
    (simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂) oa >>=
     (fun x => simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂) (f x))) :=
by simp only [simulateQ_bind, Function.comp_def]

/--
**SimOracle2 Pure Simplification**

Simulating a pure value results in the pure value itself.
-/
@[simp]
lemma simulateQ_simOracle2_pure (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i) {α : Type} (x : α) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂) (pure x) = pure x :=
by simp [simulateQ_pure]

/--
**SimOracle2 Base Lift Lemma**

Simulating a computation that only uses the base oracles (lifted to the larger spec)
results in the original computation.
-/
@[simp]
lemma simulateQ_simOracle2_liftComp (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    {α : Type} (oa : OracleComp oSpec α) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂) (liftComp oa _) = oa :=
by
  rw [simulateQ_liftComp]
  have : QueryImpl.lift (OracleInterface.simOracle2 oSpec t₁ t₂) = idOracle :=
    by ext β q; cases q; rfl
  rw [this, idOracle.simulateQ_eq]

/-- Simulating a query to the first transcript in simOracle2 resolves to its pure answer. -/
@[simp]
lemma simulateQ_simOracle2_query_inr_inl (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (i : ι₁) (t : [T₁]ₒ.domain i) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (query (spec := oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)) (.inr (.inl i)) t)) =
    pure (OracleInterface.answer (t₁ i) t) :=
by
  simp only [simulateQ_query, OracleInterface.simOracle2]
  unfold SimOracle.append fnOracle
  rfl

/-- Simulating a query to the second transcript in simOracle2 resolves to its pure answer. -/
@[simp]
lemma simulateQ_simOracle2_query_inr_inr (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (i : ι₂) (t : [T₂]ₒ.domain i) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (query (spec := oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)) (.inr (.inr i)) t)) =
    pure (OracleInterface.answer (t₂ i) t) :=
by
  simp only [simulateQ_query, OracleInterface.simOracle2]
  unfold SimOracle.append fnOracle
  rfl

/-- Simulating a query to the base oracles in simOracle2 passes through to the underlying oracle. -/
@[simp]
lemma simulateQ_simOracle2_query_inl (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (i : ι) (t : oSpec.domain i) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (query (spec := oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)) (.inl i) t)) =
    query i t :=
by
  simp only [simulateQ_query, OracleInterface.simOracle2]
  unfold SimOracle.append idOracle
  rfl

/--
**Generic Simulation Reduction**

This lemma reduces `simulateQ (simOracle2 ...) (liftM q)` to the
raw implementation `(simOracle2 ...).impl q`.

This allows you to eliminate `simulateQ` even if the specific query index
is generic or unknown at the moment.
-/
@[simp]
lemma simulateQ_simOracle2_liftM
    {ι : Type u} {oSpec : OracleSpec ι} [oSpec.FiniteRange]
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    {α : Type} (q : (oSpec ++ₒ ([T₁]ₒ ++ₒ [T₂]ₒ)).OracleQuery α) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂) (liftM q) =
    (OracleInterface.simOracle2 oSpec t₁ t₂).impl q := by
  -- This follows directly from the definition of simulateQ on a single query
  simp only [simulateQ_query]

/-- Unfolds simOracle2 implementation for transcript 1. -/
@[simp]
lemma simOracle2_impl_inr_inl
    {ι : Type u} {oSpec : OracleSpec ι} [oSpec.FiniteRange]
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (i : ι₁) (t : ([T₁]ₒ).domain i) :
    (OracleInterface.simOracle2 oSpec t₁ t₂).impl (query (.inr (.inl i)) t) =
    pure (OracleInterface.answer (t₁ i) t) :=
by rfl

/-- Unfolds simOracle2 implementation for transcript 2. -/
@[simp]
lemma simOracle2_impl_inr_inr
    {ι : Type u} {oSpec : OracleSpec ι} [oSpec.FiniteRange]
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (i : ι₂) (t : ([T₂]ₒ).domain i) :
    (OracleInterface.simOracle2 oSpec t₁ t₂).impl (query (.inr (.inr i)) t) =
    pure (OracleInterface.answer (t₂ i) t) :=
by rfl

/-- Unfolds simOracle2 implementation for base queries. -/
@[simp]
lemma simOracle2_impl_inl
    {ι : Type u} {oSpec : OracleSpec ι} [oSpec.FiniteRange]
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (i : ι) (t : oSpec.domain i) :
    (OracleInterface.simOracle2 oSpec t₁ t₂).impl (query (.inl i) t) =
    query i t :=
by rfl

/--
**Step 2 Helper: Collapse Monadic Bind and Composition**
This lemma resolves the pattern `pure x >>= (simulateQ ∘ f)` that often appears
when simulating sequential code. It forces the function `f` to be applied to `x`
inside the simulation immediately.
-/
@[simp]
lemma bind_pure_simulateQ_comp
    {ι ι' : Type*} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (so : SimOracle.Stateless spec spec')
    {α β : Type v} (x : α) (f : α → OracleComp spec β) :
    (pure x >>= (simulateQ so ∘ f)) = simulateQ so (f x) := by rfl

/--
**SimOracle2 Implementation Reduction**

Reduces the raw implementation of `simOracle2` on a transcript query
directly to `pure value`.
-/
@[simp]
lemma simOracle2_impl_liftM_query_eq_pure
    {ι : Type u} {oSpec : OracleSpec ι} [oSpec.FiniteRange]
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (i : ι₂) (t : ([T₂]ₒ).domain i) :
    (OracleInterface.simOracle2 oSpec t₁ t₂).impl (liftM (query (spec := [T₂]ₒ) i t)) =
    pure (OracleInterface.answer (t₂ i) t) := by
  simp only [liftM]
  rfl

/--
**SimOracle2 Implementation Reduction (T1)**

Reduces the raw implementation of `simOracle2` on a transcript 1 query
directly to `pure value`.
-/
@[simp]
lemma simOracle2_impl_liftM_query_eq_pure_inl
    {ι : Type u} {oSpec : OracleSpec ι} [oSpec.FiniteRange]
    {ι₁ : Type v} {T₁ : ι₁ → Type w} [∀ i, OracleInterface (T₁ i)]
    {ι₂ : Type v} {T₂ : ι₂ → Type w} [∀ i, OracleInterface (T₂ i)]
    (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (i : ι₁) (t : ([T₁]ₒ).domain i) :
    (OracleInterface.simOracle2 oSpec t₁ t₂).impl (liftM (query (spec := [T₁]ₒ) i t)) =
    pure (OracleInterface.answer (t₁ i) t) := by
  simp only [liftM]
  rfl

end SimOracleSafety
