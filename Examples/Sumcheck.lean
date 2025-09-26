import ArkLib

/-!
# Minimal walkthrough of ArkLib
-/

set_option linter.style.longLine false

universe u v w

open Polynomial Bivariate NNReal

local instance {F : Type*} [Field F] : Nonempty F := ⟨0⟩

namespace Example

/-! ## First, we define the type of oracle computations, which forms our base monad -/

structure OracleSpec where
  Query : Type u
  Response : Query → Type v

namespace OracleSpec

/-- Combine two oracle specifications by taking the disjoint union of their query types. -/
def add (spec : OracleSpec) (spec' : OracleSpec) : OracleSpec :=
  { Query := spec.Query ⊕ spec'.Query
    Response := Sum.elim spec.Response spec'.Response }

/-- Create an oracle specification with a single query type `Q` and constant response type `R`. -/
def single (Q : Type u) (R : Type v) : OracleSpec :=
  { Query := Q
    Response := fun _ => R }

instance : Add OracleSpec where
  add := add

protected class Fintype (spec : OracleSpec) where
  [instQuery : Fintype spec.Query]
  [instResponse : ∀ q, Fintype (spec.Response q)]

instance {spec : OracleSpec} [spec.Fintype] : Fintype spec.Query := Fintype.instQuery
instance {spec : OracleSpec} [spec.Fintype] (q : spec.Query) : Fintype (spec.Response q) :=
  Fintype.instResponse q

protected class Nonempty (spec : OracleSpec) where
  [instQuery : Nonempty spec.Query]
  [instResponse : ∀ q, Nonempty (spec.Response q)]

instance {spec : OracleSpec} [spec.Nonempty] : Nonempty spec.Query := Nonempty.instQuery
instance {spec : OracleSpec} [spec.Nonempty] (q : spec.Query) : Nonempty (spec.Response q) :=
  Nonempty.instResponse q

end OracleSpec

inductive OracleComp (spec : OracleSpec) (α : Type w) where
  | pure (a : α) : OracleComp spec α
  | queryBind (q : spec.Query) (cont : spec.Response q → OracleComp spec α) : OracleComp spec α

namespace OracleComp

variable {spec spec' : OracleSpec} {α β : Type w}

/-- Make a single oracle query and return the response. -/
def query (q : spec.Query) : OracleComp spec (spec.Response q) :=
  queryBind q pure

/-- Monadic bind for oracle computations. -/
def bind (oa : OracleComp spec α) (f : α → OracleComp spec β) : OracleComp spec β :=
  match oa with
  | pure a => f a
  | queryBind q cont => queryBind q (fun r => bind (cont r) f)

instance : Monad (OracleComp spec) where
  pure := OracleComp.pure
  bind := OracleComp.bind

@[simp]
lemma pure_eq_monad_pure (x : α) : OracleComp.pure x = (pure x : OracleComp spec α) := rfl

@[simp]
lemma bind_eq_monad_bind (oa : OracleComp spec α) (f : α → OracleComp spec β) :
    OracleComp.bind oa f = (oa >>= f : OracleComp spec β) := rfl

instance : LawfulMonad (OracleComp spec) :=
  LawfulMonad.mk' (OracleComp spec)
    (fun x => by
      induction x with
      | pure a => rfl
      | queryBind q cont ih =>
          exact congr_arg (OracleComp.queryBind q) (funext (fun r => ih r)))
    (fun x f => rfl)
    (fun x f g => by
      induction x with
      | pure a => rfl
      | queryBind q cont ih =>
          exact congr_arg (OracleComp.queryBind q) (funext (fun r => ih r)))

/-- Lift an oracle computation from the left component of a sum specification. -/
def inl (oa : OracleComp spec α) : OracleComp (spec + spec') α :=
  match oa with
  | pure a => pure a
  | queryBind q cont => queryBind (.inl q) (fun r => inl (cont r))

/-- Lift an oracle computation from the right component of a sum specification. -/
def inr (oa : OracleComp spec' α) : OracleComp (spec + spec') α :=
  match oa with
  | pure a => pure a
  | queryBind q cont => queryBind (.inr q) (fun r => inr (cont r))

instance : MonadLift (OracleComp spec) (OracleComp (spec + spec')) where
  monadLift := inl

instance : MonadLift (OracleComp spec') (OracleComp (spec + spec')) where
  monadLift := inr

section Support

def support (oa : OracleComp spec α) : Set α :=
  match oa with
  | pure a => {a}
  | queryBind q cont => ⋃ x : spec.Response q, support (cont x)

@[simp]
lemma support_pure (a : α) : support (pure a : OracleComp spec α) = {a} := rfl

@[simp]
lemma support_queryBind (q : spec.Query) (cont : spec.Response q → OracleComp spec α) :
    support (queryBind q cont) = ⋃ x : spec.Response q, support (cont x) := rfl

@[simp]
lemma support_bind (oa : OracleComp spec α) (f : α → OracleComp spec β) :
    support (oa >>= f) = ⋃ x : oa.support, support (f x) := by
  induction oa with
  | pure a => simp; rfl
  | queryBind q cont ih => simp [support_queryBind]; sorry

end Support

section EvalDist

variable [spec.Fintype] [spec.Nonempty]

-- Distributional semantics via responding uniformly at random
noncomputable def evalDist (oa : OracleComp spec α) : PMF α :=
  match oa with
  | pure a => PMF.pure a
  | queryBind q cont => do
      let r ← PMF.uniformOfFintype (spec.Response q)
      evalDist (cont r)

noncomputable instance instHasEvalDist : HasEvalDist (OptionT (OracleComp spec)) where
  evalDist := fun oa => evalDist (oa.run)
  evalDist_pure := fun x => by simp [evalDist]; rfl
  evalDist_bind := fun oa cont => sorry

end EvalDist

end OracleComp

/-! ## Next, we define the type of protocol specifications and interactive protocols with a given spec -/

/-- A direction of a message in an interactive protocol: one either sends or receives a message -/
inductive Direction where | Send | Receive

namespace Direction

/-- Flip the direction of a message: Send becomes Receive and vice versa. -/
def flip : Direction → Direction
  | Send => Receive
  | Receive => Send

end Direction

@[reducible]
def ProtocolSpec := List (Direction × Type)

namespace ProtocolSpec

/-- Flip all message directions in a protocol specification. -/
def flip : ProtocolSpec → ProtocolSpec
  | [] => []
  | (dir, T) :: pSpec => (dir.flip, T) :: flip pSpec

end ProtocolSpec

/-- The type of transcripts for a given protocol specification.
    A transcript records all messages exchanged during protocol execution. -/
def Transcript : (pSpec : ProtocolSpec) → Type
  | [] => Unit
  | (_, T) :: pSpec => T × Transcript pSpec

/-- An interactive protocol in monad `m` following specification `pSpec` and producing `Output`.
    - For empty spec: just the output
    - For Send step: a message paired with continuation
    - For Receive step: a function expecting a message and returning continuation -/
def InteractiveProtocol (m : Type → Type) (pSpec : ProtocolSpec) (Output : Type) : Type :=
  match pSpec with
  | [] => Output
  | (.Send, T) :: pSpec => T × m (InteractiveProtocol m pSpec Output)
  | (.Receive, T) :: pSpec => T → m (InteractiveProtocol m pSpec Output)

/-- A prover takes an input statement and witness, and produces an interactive protocol
    that outputs a statement-witness pair. -/
def Prover (m : Type → Type) (InputStatement InputWitness : Type) (OutputStatement OutputWitness : Type)
    (pSpec : ProtocolSpec) : Type :=
  InputStatement × InputWitness → InteractiveProtocol m pSpec (OutputStatement × OutputWitness)

/-- A verifier takes an input statement and produces an interactive protocol
    (with flipped message directions) that outputs a statement. -/
def Verifier (m : Type → Type) (InputStatement OutputStatement : Type) (pSpec : ProtocolSpec) : Type :=
  InputStatement → InteractiveProtocol m pSpec.flip OutputStatement

namespace InteractiveProtocol

variable {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] [MonadLiftT m₁ m₂]

/-- Change the monad of an interactive protocol by lifting its internal effects. -/
@[simp]
def liftM (pSpec : ProtocolSpec)
    {Output : Type} :
    InteractiveProtocol m₁ pSpec Output → InteractiveProtocol m₂ pSpec Output :=
  match pSpec with
  | [] => fun ip => ip
  | (.Send, _) :: ps => fun ip =>
      match ip with
      | (msg, cont) =>
        (msg, monadLift (do
          let rest ← cont
          pure (liftM ps rest)))
  | (.Receive, _) :: ps => fun ip =>
      (fun t => monadLift (do
        let rest ← ip t
        pure (liftM ps rest)))

/-- Execute an interactive protocol by coordinating message exchanges between two parties.
    Returns the complete transcript along with both parties' outputs. -/
def run {m : Type → Type} [Monad m] {protocolSpec : ProtocolSpec} {Output₁ Output₂ : Type}
    (sender : InteractiveProtocol m protocolSpec Output₁)
    (receiver : InteractiveProtocol m protocolSpec.flip Output₂) :
    m (Transcript protocolSpec × Output₁ × Output₂) :=
  match protocolSpec with
  | [] =>
    -- Base case: no more messages to exchange
    let receiverOutput := receiver
    let senderOutput := sender
    pure ((), senderOutput, receiverOutput)
  | (.Send, _) :: remainingSpec =>
    -- Sender transmits a message to receiver
    match sender, receiver with
    | (message, senderContinuation), receiverFunction => do
        -- Receiver processes the message and produces next protocol state
        let receiverNext ← receiverFunction message
        -- Sender continues with next protocol state
        let senderNext ← senderContinuation
        -- Recursively execute remaining protocol
        let ⟨transcript, senderOutput, receiverOutput⟩ ← @run m _ remainingSpec _ _ senderNext receiverNext
        pure ((message, transcript), senderOutput, receiverOutput)
  | (.Receive, _) :: remainingSpec =>
    -- Receiver transmits a message to sender
    match sender, receiver with
    | senderFunction, (message, receiverContinuation) => do
        -- Sender processes the message and produces next protocol state
        let senderNext ← senderFunction message
        -- Receiver continues with next protocol state
        let receiverNext ← receiverContinuation
        -- Recursively execute remaining protocol
        let ⟨transcript, senderOutput, receiverOutput⟩ ← @run m _ remainingSpec _ _ senderNext receiverNext
        pure ((message, transcript), senderOutput, receiverOutput)

end InteractiveProtocol

/-- An (interactive oracle) reduction consists of a prover and a verifier -/
structure Reduction (mP mV : Type → Type)
    (InputStatement InputWitness : Type)
    (OutputStatement OutputWitness : Type)
    (pSpec : ProtocolSpec) where
  prover : Prover mP InputStatement InputWitness OutputStatement OutputWitness pSpec
  verifier : Verifier mV InputStatement OutputStatement pSpec

namespace Reduction

variable {mP mV : Type → Type} {m : Type → Type}
  [Monad mP] [Monad mV] [Monad m] [MonadLiftT mP m] [MonadLiftT mV m] [HasEvalDist m]
  {InputStatement InputWitness : Type}
  {OutputStatement OutputWitness : Type}
  {pSpec : ProtocolSpec}

/-- Execute a reduction by running the interactive protocol between prover and verifier.
    Takes an input statement and witness, applies the reduction's prover and verifier strategies,
    and returns the complete execution trace along with both parties' outputs. -/
def run (inputStatement : InputStatement) (inputWitness : InputWitness)
    (reduction : Reduction mP mV InputStatement InputWitness OutputStatement OutputWitness pSpec) :
      m (Transcript pSpec × (OutputStatement × OutputWitness) × OutputStatement) :=
  -- Initialize prover with input statement and witness
  let initialProverProtocol := reduction.prover (inputStatement, inputWitness)
  -- Initialize verifier with input statement
  let initialVerifierProtocol := reduction.verifier inputStatement
  -- Lift both protocols to the common monad m
  let liftedProverProtocol : InteractiveProtocol m pSpec (OutputStatement × OutputWitness) :=
    InteractiveProtocol.liftM pSpec initialProverProtocol
  let liftedVerifierProtocol : InteractiveProtocol m pSpec.flip OutputStatement :=
    InteractiveProtocol.liftM pSpec.flip initialVerifierProtocol
  -- Execute the interactive protocol between the two parties
  InteractiveProtocol.run liftedProverProtocol liftedVerifierProtocol

/-- Perfect completeness of a reduction: for every input statement and witness, if the input
relation holds, then the output relation holds with probability 1. -/
def completeness
    (inputRelation : Set (InputStatement × InputWitness))
    (outputRelation : Set (OutputStatement × OutputWitness))
    (reduction : Reduction mP mV InputStatement InputWitness OutputStatement OutputWitness pSpec) :
      Prop :=
  ∀ inputStatement : InputStatement,
  ∀ inputWitness : InputWitness,
    (inputStatement, inputWitness) ∈ inputRelation →
      Pr[ fun ⟨_, ⟨prvOutputStatement, outputWitness⟩, verOutputStatement⟩
          => (verOutputStatement, outputWitness) ∈ outputRelation
              ∧ prvOutputStatement = verOutputStatement
          | reduction.run (m := m) inputStatement inputWitness] = 1

end Reduction

namespace Verifier

variable {mV : Type → Type} [Monad mV]
  {InputStatement OutputStatement : Type} {pSpec : ProtocolSpec}

/-- Soundness of a reduction: given an input statement not in the input language,
  any **arbitrary** prover interacting with the verifier will cause the verifier to output an
  output statement not in the output language,
  **except** with probability at most `soundnessError`. -/
def soundness
    (inputLanguage : Set InputStatement)
    (outputLanguage : Set OutputStatement)
    (verifier : Verifier mV InputStatement OutputStatement pSpec)
    (m : Type → Type) [Monad m] [HasEvalDist m] [MonadLiftT mV m]
    (soundnessError : ℝ≥0) : Prop :=
  ∀ inputStatement : InputStatement,
  -- Prover strategy without inputs or outputs
  ∀ prover : InteractiveProtocol m pSpec Unit,
    inputStatement ∉ inputLanguage →
    Pr[ fun ⟨_, _, outputStatement⟩ => outputStatement ∈ outputLanguage
      | InteractiveProtocol.run (m := m) prover (verifier inputStatement).liftM] ≤ soundnessError

end Verifier

/-! ## We specify the (two-round) sum-check protocol based on our definitions -/

namespace Sumcheck

/- The (two-round) sum-check protocol specification:

Public parameter: `F : Type` is a finite field, and `d : ℕ` the degree bound

Input statement:
- a bivariate polynomial `p(X, Y) ∈ F[X][Y]` of degree at most `d` in each variable,
- a target `t : F`

Input witness: none (everything is public)

Input relation: `p(0, 0) + p(0, 1) + p(1, 0) + p(1, 1) = t`

1. The prover sends a univariate polynomial `s₁(X) ∈ F[X]`,
claimed to be equal to `p(X, 0) + p(X, 1)`

2. The verifier checks that `deg s₁ ≤ d` and `s₁(0) + s₁(1) = t`,
then sends a random challenge `r₁ : F`

3. The prover sends a univariate polynomial `s₂(X) ∈ F[X]`,
claimed to be equal to `p(r₁, X)`

4. The verifier checks that `deg s₂ ≤ d` and `s₂(0) + s₂(1) = s₁(r₁)`,
then sends a random challenge `r₂ : F` and sets the output claim to `t₂ := s₂(r₂)`

Output statement:
- same bivariate polynomial `p(X, Y)`
- challenges `r₁ : F` and `r₂ : F`
- output claim `t₂ : F`

Output witness: none (everything is public)

Output relation: `p(r₁, r₂) = t₂`
-/

variable (F : Type) [Field F] [Fintype F] (d : ℕ)

/-- The protocol specification, from the point of view of the prover. -/
def pSpec : ProtocolSpec := [(.Send, F[X]), (.Receive, F), (.Send, F[X]), (.Receive, F)]

/- Sanity check on the type of transcript of the protocol specification -/
#reduce (types := true) Transcript (pSpec F)

/-- The field sampling oracle: given a dummy query `()`, returns a random element of `F` -/
@[reducible]
def fieldSamplingOracle : OracleSpec :=
  { Query := Unit, Response := fun _ => F }

instance : OracleSpec.Fintype (fieldSamplingOracle F) :=
  { instQuery := inferInstance
    instResponse := inferInstance }

instance : OracleSpec.Nonempty (fieldSamplingOracle F) :=
  { instQuery := inferInstance
    instResponse := inferInstance }

/-- Sample a random field element -/
def sampleField : OracleComp (fieldSamplingOracle F) F := OracleComp.query ()

/-- The bivariate polynomial evaluation oracle: given `(x, y)`, returns `p(x, y)` -/
def bivariatePolyOracle : OracleSpec :=
  { Query := F × F, Response := fun _ => F }

/-- Query polynomial evaluation at point (x,y) -/
def queryEvalXY (point : F × F) : OracleComp (bivariatePolyOracle F) F := OracleComp.query point

/-- Input: polynomial p(X,Y) of degree ≤ d and target sum t -/
def InputStatement := F⦃≤ d⦄[X][Y] × F

/-- No witness needed (everything is public) -/
def InputWitness := Unit

/-- Input relation: p(0,0) + p(0,1) + p(1,0) + p(1,1) = t -/
def inputRelation : Set (InputStatement F d × InputWitness) :=
  fun ⟨⟨⟨p, _⟩, t⟩, _⟩ => p.evalXY 0 0 + p.evalXY 0 1 + p.evalXY 1 0 + p.evalXY 1 1 = t

/-- Output: polynomial p, challenges r₁, r₂, and final claim t₂ -/
def OutputStatement : Type := F⦃≤ d⦄[X][Y] × F × F × F

/-- No witness needed (everything is public) -/
def OutputWitness := Unit

/-- Output relation: p(r₁, r₂) = t₂ -/
def outputRelation : Set (OutputStatement F d × OutputWitness) :=
  fun ⟨⟨⟨p, _⟩, r₁, r₂, t₂⟩, _⟩ => p.evalXY r₁ r₂ = t₂

noncomputable section

/-- Prover strategy: compute s₁ = p(X,0) + p(X,1), then s₂ = p(r₁,X) -/
def prover : Prover Id
    (InputStatement F d) InputWitness (OutputStatement F d) OutputWitness (pSpec F) :=
  fun ⟨⟨⟨p, h⟩, _⟩, _⟩ => Id.run do
    -- Step 1: Send s₁(X) = p(X,0) + p(X,1)
    let s₁ : F[X] := p.evalY 0 + p.evalY 1
    return (s₁, fun r₁ => do
      -- Step 3: Send s₂(X) = p(r₁,X)
      let s₂ : F[X] := p.evalX r₁
      return (s₂, fun r₂ => do
        -- Output: (p, r₁, r₂, p(r₁,r₂))
        return ((⟨p, h⟩, r₁, r₂, p.evalXY r₁ r₂), ())))

open Classical in
/-- Verifier strategy: check degree bounds, consistency, and sample random challenges -/
def verifier : Verifier (OptionT (OracleComp (fieldSamplingOracle F)))
    (InputStatement F d) (OutputStatement F d) (pSpec F) :=
  fun ⟨p, t⟩ s₁ => do
      -- Step 2: Check deg s₁ ≤ d and s₁(0) + s₁(1) = t, then sample r₁
      let r₁ : F ← sampleField F
      guard (s₁.degree ≤ d)
      guard (s₁.eval 0 + s₁.eval 1 = t)
      return (r₁, do return fun s₂ => do
        -- Step 4: Check deg s₂ ≤ d and s₂(0) + s₂(1) = s₁(r₁), then sample r₂ and set new claim `t₂ := s₂(r₂)`
        let r₂ : F ← sampleField F
        guard (s₂.degree ≤ d)
        guard (s₂.eval 0 + s₂.eval 1 = s₁.eval r₁)
        let t₂ := s₂.eval r₂
        return (r₂, pure (p, r₁, r₂, t₂)))

/-- The (two-round) sum-check protocol as a reduction -/
def reduction : Reduction
    Id (OptionT (OracleComp (fieldSamplingOracle F)))
    (InputStatement F d) InputWitness (OutputStatement F d) OutputWitness (pSpec F) where
  prover := prover F d
  verifier := verifier F d

theorem reduction_completeness :
    (reduction F d).completeness (m := OptionT (OracleComp (fieldSamplingOracle F)))
    (inputRelation F d) (outputRelation F d) := by
  intro inputStatement inputWitness isValid
  simp [reduction, Reduction.run]
  sorry

theorem reduction_soundness :
    (verifier F d).soundness (m := OptionT (OracleComp (fieldSamplingOracle F)))
    (inputRelation F d).language (outputRelation F d).language
    ((2 * d : ℝ≥0) / Fintype.card F) := by
  intro inputStatement inputWitness isValid
  sorry

end

end Sumcheck

end Example
