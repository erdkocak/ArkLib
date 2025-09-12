import Mathlib
import ArkLib.OracleReduction.OracleInterface
import ArkLib.OracleReduction.Prelude
import ArkLib.Data.Fin.Fold
import ArkLib.Data.Fin.Tuple.Lemmas

/-!
# (Ongoing) Refactor of `ProtocolSpec` to be `List` rather than `Fin`-indexed vectors

There are pros and cons:

Pros:
- One fewer layer of dependency - no need to have number of messages exchanged as an explicit
  parameter, allowing more things to be of the same type
- `List.TProd` for transcript is nice that we can pattern-match into iterated product type
- Defining interactive prover & sequential composition is much easier, does not require much (if at
  all) casting

Cons:
- There are still many cases where we want to index into `Fin pSpec.length` or similar things. This
  indexing doesn't behave as nicely (i.e. with respect to appends, etc)
- One particular problem with that is the semantics of partial protocols - `PartialTranscript`, etc.
  We don't enjoy the nice definitional equality that `Fin.take n (le_refl _) v = v`. This spills
  over into appending messages into `PartialTranscript`, indexing for message and challenge indices,
  oracle indexing for oracle verifier, etc.

-/

universe u v

@[simp]
lemma howisthisnotalemma {n : ℕ} : 0 % (n + 1) = 0 := rfl

namespace List

-- Given a list, needs a list of types with the same length (for `PrvState` construction)
def TypeList {α : Type u} (l : List α) : Type (v + 1) := l.TProd (fun _ => Type v)

-- Ideally, we want `take (n + 1)` to be `take n ++ [l[n]]`.

-- Can we achieve this?

-- Define: `take 0 = []` no matter what
-- `take (n + 1) = take n ++ [l[n]]`

def takeChecked {α : Type*} (n : ℕ) (l : List α) (h : n ≤ l.length) : List α :=
  match n with
  | 0 => []
  | n + 1 => takeChecked n l (Nat.le_of_succ_le h) ++ [l[n]]

@[simp]
lemma takeChecked_zero {α : Type*} (l : List α) :
    takeChecked 0 l (zero_le _) = [] := rfl

@[simp]
lemma takeChecked_succ {α : Type*} (n : ℕ) (l : List α) (h : n + 1 ≤ l.length) :
    takeChecked (n + 1) l h = takeChecked n l (Nat.le_of_succ_le h) ++ [l[n]] := rfl

lemma takeChecked_eq_take {α : Type*} (n : ℕ) (l : List α) (h : n ≤ l.length) :
    takeChecked n l h = take n l := by
  induction n with
  | zero => rfl
  | succ n ih => simp [take_succ, ih]

@[simp]
lemma takeChecked_length {α : Type*} (l : List α) : takeChecked l.length l (le_refl _) = l := by
  simp [takeChecked_eq_take]

variable {ι : Type v}

/-- Occurrence membership in a list, distinguishing duplicates. -/
inductive Member (i : ι) : List ι → Type v where
  | head (is : List ι) : Member i (i :: is)
  | tail (j : ι) (is : List ι) : Member i is → Member i (j :: is)

namespace Member

variable {i : ι}

/-- Inject a membership witness into the tail of a cons: `is ⊆ j :: is`. -/
def consTail (j : ι) {is : List ι} : Member i is → Member i (j :: is)
  | m => Member.tail j is m
@[simp] lemma consTail_eq {j : ι} {is : List ι} (m : Member i is) :
    consTail (i:=i) j m = Member.tail j is m := rfl

/-- Transport a membership witness from `l₁` to `l₁ ++ l₂` (left injection). -/
def mapLeft : ∀ {l₁ l₂ : List ι}, Member i l₁ → Member i (l₁ ++ l₂)
  | _ :: is, l₂, Member.head _ => by
      simpa using (Member.head (is ++ l₂))
  | j :: is, l₂, Member.tail _ _ m =>
      Member.tail j (is ++ l₂) (mapLeft (l₁:=is) (l₂:=l₂) m)
@[simp] lemma mapLeft_head {is l₂ : List ι} :
    mapLeft (i:=i) (l₁:=i :: is) (l₂:=l₂) (Member.head is) = Member.head (is ++ l₂) := rfl
@[simp] lemma mapLeft_tail {j : ι} {is l₂ : List ι} (m : Member i is) :
    mapLeft (i:=i) (l₁:=j :: is) (l₂:=l₂) (Member.tail j is m)
      = Member.tail j (is ++ l₂) (mapLeft (i:=i) (l₁:=is) (l₂:=l₂) m) := rfl

/-- Transport a membership witness from `l₂` to `l₁ ++ l₂` (right injection). -/
def mapRight : ∀ (l₁ : List ι) {l₂ : List ι}, Member i l₂ → Member i (l₁ ++ l₂)
  | [],      _, m => m
  | j :: js, l₂, m => Member.tail j (js ++ l₂) (mapRight js m)
@[simp] lemma mapRight_nil {l₂ : List ι} (m : Member i l₂) :
    mapRight (i:=i) ([] : List ι) m = m := rfl
@[simp] lemma mapRight_cons {j : ι} {js l₂ : List ι} (m : Member i l₂) :
    mapRight (i:=i) (j :: js) m = Member.tail j (js ++ l₂) (mapRight (i:=i) js m) := rfl

/-- The witness for the appended last element in `l ++ [i]`. -/
def last : ∀ (l : List ι), Member i (l ++ [i])
  | []      => Member.head []
  | j :: js => Member.tail j (js ++ [i]) (last js)
@[simp] lemma last_nil : last (i:=i) ([] : List ι) = Member.head [] := rfl
@[simp] lemma last_cons {j : ι} {js : List ι} :
    last (i:=i) (j :: js) = Member.tail j (js ++ [i]) (last (i:=i) js) := rfl

end Member

namespace TProd

variable {ι : Type v} {α : ι → Type u}

@[simp]
lemma nil_eq {ι : Type*} {α : ι → Type*} {v : List.TProd α []} : v = PUnit.unit := rfl

@[simp]
lemma cons_eq {i : ι} {is : List ι} : TProd α (i :: is) = ((α i) × TProd α is) := rfl

def get {l : List ι} (t : l.TProd α) (n : Nat) {i : ι} (hi : l[n]? = some i) : α i :=
  match l, t, n, hi with
  | _ :: _, (a, _), 0, rfl => a
  | _ :: _, (_, as), n + 1, hi => get as n hi

/-- Project a component from `t : TProd α l` using an occurrence witness `m : Member i l`. -/
def getMember {l : List ι} (t : TProd α l) {i : ι} : Member i l → α i :=
  match l, t with
  | [], _ => fun m => nomatch m
  | _ :: _, (a, as) => fun m =>
      match m with
      | Member.head _ => a
      | Member.tail _ _ m' => getMember as m'

@[simp] theorem getMember_head {i : ι} {l : List ι} (t : TProd α (i :: l)) :
    getMember (l := i :: l) t (i := i) (Member.head l) = t.1 := rfl

@[simp] theorem getMember_tail {i j : ι} {l : List ι} (t : TProd α (j :: l)) (m : Member i l) :
    getMember (l := j :: l) t (i := i) (Member.tail j l m) = getMember (l := l) t.2 m := rfl

/-! ### Append and concat on `TProd` -/

/-- Append two iterated products, corresponding to list concatenation on indices. -/
def append {l₁ l₂ : List ι} (t₁ : TProd α l₁) (t₂ : TProd α l₂) : TProd α (l₁ ++ l₂) :=
  match l₁, t₁ with
  | [], _ => t₂
  | _ :: _, (a, as) => (a, append as t₂)

@[simp] theorem append_nil {l₂ : List ι} (t₂ : TProd α l₂) :
    append (l₁:=[]) (l₂:=l₂) (t₁:=PUnit.unit) t₂ = t₂ := rfl

@[simp] theorem append_cons {i : ι} {is l₂ : List ι}
    (a : α i) (as : TProd α is) (t₂ : TProd α l₂) :
    append (l₁:=i :: is) (l₂:=l₂) (t₁:=(a, as)) t₂ = (a, append as t₂) := rfl

/-- Append a single component at the end, corresponding to `l ++ [i]`. -/
def concat {l : List ι} (t : TProd α l) {i : ι} (a : α i) : TProd α (l ++ [i]) :=
  append t (a, PUnit.unit)

@[simp] theorem concat_nil {i : ι} (a : α i) :
    concat (α:=α) (l:=[]) (t:=PUnit.unit) a = (a, PUnit.unit) := rfl

@[simp]
theorem concat_cons {i : ι} {is : List ι} (a₀ : α i) (as : TProd α is)
    {j : ι} (a : α j) :
    concat (α:=α) (l:=i :: is) (t:=(a₀, as)) a = (a₀, concat (α:=α) (l:=is) (t:=as) a) := rfl

-- Missing definition: given a partial transcript (defined as the transcript of the protocol cut off
-- by some index), append a message of the next round's type to it

-- Can't think of a way for this _not_ to use some kind of casting...

def concatNext {l : List ι} (n : ℕ) (h : n < l.length)
    (t : TProd α (l.takeChecked n (by omega))) (a : α l[n]) :
    TProd α (l.takeChecked (n + 1) (by omega)) :=
  concat t a

/-- The first half of a `TProd` of an appended list -/
def fst {l₁ l₂ : List ι} (t : TProd α (l₁ ++ l₂)) : TProd α l₁ :=
  match l₁, t with
  | [], _ => PUnit.unit
  | _ :: _, (a, as) => (a, fst as)

/-- The second half of a `TProd` of an appended list -/
def snd {l₁ l₂ : List ι} (t : TProd α (l₁ ++ l₂)) : TProd α l₂ :=
  match l₁ with
  | [] => t
  | _ :: _ => snd t.2

-- TODO: figure out better way to define the cast (cast element-wise?)
def cast {l l' : List ι} (h : l = l') (t : TProd α l) : TProd α l' := h ▸ t

def cast' {l l' : List ι} (hLen : l.length = l'.length) (h : ∀ i : Fin l.length, l[i] = l'[i])
    (t : TProd α l) : TProd α l' :=
  match l, t with
  | [], _ => ((by grind [List.length_eq_zero_iff]) : l' = []) ▸ PUnit.unit
  | _ :: _, (a, as) => by simp_all; sorry

/-! #### Membership transport for cons/append/concat, and projection lemmas -/

namespace Member

variable {i : ι}

/-- Inject a membership witness into the tail of a cons: `is ⊆ j :: is`. -/
def consTail (j : ι) {is : List ι} : Member i is → Member i (j :: is)
  | m => Member.tail j is m
@[simp] lemma consTail_eq {j : ι} {is : List ι} (m : Member i is) :
    consTail (i:=i) j m = Member.tail j is m := rfl

/-- Transport a membership witness from `l₁` to `l₁ ++ l₂` (left injection). -/
def mapLeft : ∀ {l₁ l₂ : List ι}, Member i l₁ → Member i (l₁ ++ l₂)
  | _ :: is, l₂, Member.head _ => by
      simpa using (Member.head (is ++ l₂))
  | j :: is, l₂, Member.tail _ _ m =>
      Member.tail j (is ++ l₂) (mapLeft (l₁:=is) (l₂:=l₂) m)
@[simp] lemma mapLeft_head {is l₂ : List ι} :
    mapLeft (i:=i) (l₁:=i :: is) (l₂:=l₂) (Member.head is) = Member.head (is ++ l₂) := rfl
@[simp] lemma mapLeft_tail {j : ι} {is l₂ : List ι} (m : Member i is) :
    mapLeft (i:=i) (l₁:=j :: is) (l₂:=l₂) (Member.tail j is m)
      = Member.tail j (is ++ l₂) (mapLeft (i:=i) (l₁:=is) (l₂:=l₂) m) := rfl

/-- Transport a membership witness from `l₂` to `l₁ ++ l₂` (right injection). -/
def mapRight : ∀ (l₁ : List ι) {l₂ : List ι}, Member i l₂ → Member i (l₁ ++ l₂)
  | [],      _, m => m
  | j :: js, l₂, m => Member.tail j (js ++ l₂) (mapRight js m)
@[simp] lemma mapRight_nil {l₂ : List ι} (m : Member i l₂) :
    mapRight (i:=i) ([] : List ι) m = m := rfl
@[simp] lemma mapRight_cons {j : ι} {js l₂ : List ι} (m : Member i l₂) :
    mapRight (i:=i) (j :: js) m = Member.tail j (js ++ l₂) (mapRight (i:=i) js m) := rfl

/-- The witness for the appended last element in `l ++ [i]`. -/
def last : ∀ (l : List ι), Member i (l ++ [i])
  | []      => Member.head []
  | j :: js => Member.tail j (js ++ [i]) (last js)
@[simp] lemma last_nil : last (i:=i) ([] : List ι) = Member.head [] := rfl
@[simp] lemma last_cons {j : ι} {js : List ι} :
    last (i:=i) (j :: js) = Member.tail j (js ++ [i]) (last (i:=i) js) := rfl

end Member

@[simp]
theorem getMember_cons_tail {j : ι} {is : List ι}
    (t : TProd α (j :: is)) {i : ι} (m : Member i is) :
    getMember (l := j :: is) t (Member.consTail (j:=j) m) = getMember (l := is) t.2 m := rfl

@[simp]
theorem getMember_append_left {l₁ l₂ : List ι}
    (t₁ : TProd α l₁) (t₂ : TProd α l₂) {i : ι} (m : Member i l₁) :
    getMember (l := l₁ ++ l₂) (append t₁ t₂) (Member.mapLeft (l₁:=l₁) (l₂:=l₂) m)
      = getMember (l := l₁) t₁ m := by
  revert t₁
  induction m with
  | head is =>
      intro t₁; cases t₁ with
      | _ => rfl
  | tail j is m ih =>
      intro t₁; cases t₁ with
      | _ a as =>
        simpa [append, getMember] using ih as

@[simp]
theorem getMember_append_right {l₁ l₂ : List ι}
    (t₁ : TProd α l₁) (t₂ : TProd α l₂) {i : ι} (m : Member i l₂) :
    getMember (l := l₁ ++ l₂) (append t₁ t₂) (Member.mapRight l₁ m)
      = getMember (l := l₂) t₂ m := by
  revert t₁
  induction l₁ with
  | nil => intro t₁; cases t₁; rfl
  | cons j js ih =>
      intro t₁; cases t₁ with
      | _ a as =>
        simpa [append, getMember] using ih as

@[simp]
theorem getMember_concat_left {l : List ι}
    (t : TProd α l) {j : ι} (a : α j) {i : ι} (m : Member i l) :
    getMember (l := l ++ [j]) (concat t a) (Member.mapLeft (l₁:=l) (l₂:=[j]) m)
      = getMember (l := l) t m := by
  revert t
  induction m with
  | head is =>
      intro t; cases t with
      | _ => rfl
  | tail k is m ih =>
      intro t; cases t with
      | _ a₀ as => simp [concat, getMember]

@[simp]
theorem getMember_concat_right {l : List ι}
    (t : TProd α l) {i : ι} (a : α i) :
    getMember (l := l ++ [i]) (concat t a) (Member.last (l:=l) (i:=i)) = a := by
  revert t
  induction l with
  | nil => intro t; cases t; rfl
  | cons j js ih =>
      intro t; cases t with
      | _ a₀ as =>
        simpa [concat, getMember] using ih as

/-! #### Algebraic lemmas for append and concat -/

@[simp]
theorem append_left_nil {l : List ι} (t : TProd α l) :
    append (l₁:=[]) (l₂:=l) (t₁:=PUnit.unit) t = t := rfl

@[simp]
theorem concat_eq_append_singleton {l : List ι} {i : ι}
    (t : TProd α l) (a : α i) :
    concat t a = append t (a, PUnit.unit) := by
  revert t
  induction l with
  | nil => intro t; cases t; rfl
  | cons j js ih =>
      intro t; cases t with
      | _ a₀ as => simp [concat, append]

end TProd
end List

def Direction.swap : Direction → Direction
  | Direction.P_to_V => Direction.V_to_P
  | Direction.V_to_P => Direction.P_to_V

def OracleSpec.ofList (l : List (Type × Type)) : OracleSpec (Fin l.length) :=
  fun i => l.get i

def OracleInterface.toOracleSpecOfList (l : List Type) [∀ i, OracleInterface (l.get i)] :
    OracleSpec (Fin l.length) :=
  fun i => (Query (l.get i), Response (l.get i))

-- instance {l₁ l₂ : List Type}
--     [∀ i, OracleInterface (l₁.get i)] [∀ i, OracleInterface (l₂.get i)] :
--     ∀ i, OracleInterface ((l₁ ++ l₂).get i) :=
--   fun i => by
--     simp at i

@[reducible]
def ProtocolSpec := List (Direction × Type)

namespace ProtocolSpec

def dir (pSpec : ProtocolSpec) : List Direction := pSpec.map Prod.fst

def «Type» (pSpec : ProtocolSpec) : List Type := pSpec.map Prod.snd

/-- Flip the direction of each element in the protocol spec -/
def flipDir (pSpec : ProtocolSpec) : ProtocolSpec :=
  pSpec.map (fun x => (x.fst.swap, x.snd))

/-- List of types of a protocol spec where the direction is `P_to_V` (message types).
Could have been defined using `List.filterMap` but it is not as nice definitionally. -/
def messageTypes : (pSpec : ProtocolSpec) → List Type
  | [] => []
  | (dir, MsgType) :: tl => match dir with
    | Direction.P_to_V => MsgType :: messageTypes tl
    | Direction.V_to_P => messageTypes tl

/-- List of types of a protocol spec where the direction is `V_to_P` (challenge types).
Could have been defined using `List.filterMap` but it is not as nice definitionally. -/
def challengeTypes : (pSpec : ProtocolSpec) → List Type
  | [] => []
  | (dir, ChalType) :: tl => match dir with
    | Direction.P_to_V => challengeTypes tl
    | Direction.V_to_P => ChalType :: challengeTypes tl

/-- Message type for a protocol spec, with length equal to the protocol spec length
(replacing each verifier's challenge type with `Unit`) -/
def Message (pSpec : ProtocolSpec) : Type := pSpec.messageTypes.TProd id

/-- Challenge type for a protocol spec, with length equal to the protocol spec length
(replacing each prover's message type with `Unit`) -/
def Challenge (pSpec : ProtocolSpec) : Type := pSpec.challengeTypes.TProd id

@[reducible]
def Transcript (pSpec : ProtocolSpec) : Type := pSpec.TProd Prod.snd

def PartialTranscript (pSpec : List (Direction × Type)) (n : Fin (pSpec.length + 1)) : Type :=
  Transcript (pSpec.takeChecked n (by omega))

namespace PartialTranscript

/-- Concatenate a partial transcript with an element (assuming this doesn't overflow the protocol
  spec) -/
def concat {pSpec : List (Direction × Type)} {n : Fin pSpec.length}
    (t : PartialTranscript pSpec n.castSucc) (a : (pSpec.get n).2) :
    PartialTranscript pSpec n.succ :=
  List.TProd.concat t a

/-- Convert a full partial transcript to a transcript, via casting the protocol spec -/
def toFull {pSpec : List (Direction × Type)} (t : PartialTranscript pSpec (Fin.last pSpec.length)) :
    Transcript pSpec :=
  List.TProd.cast (List.takeChecked_length pSpec) t

end PartialTranscript

def testPSpec : ProtocolSpec :=
  [(Direction.P_to_V, Nat), (Direction.V_to_P, Bool)]

def testTranscript : Transcript testPSpec :=
  (0, true, ())

/-- Append two protocol specs. Wrapper around `List.append` -/
def append (pSpec₁ pSpec₂ : ProtocolSpec) : ProtocolSpec :=
  pSpec₁ ++ pSpec₂

@[simp]
lemma nil_append {pSpec : ProtocolSpec} : append [] pSpec = pSpec := rfl

@[simp]
lemma append_nil {pSpec : ProtocolSpec} : append pSpec [] = pSpec := by
  simp [append]

@[simp]
lemma append_eq_cons {pSpec : ProtocolSpec} {dir : Direction} {T : Type} :
    append [(dir, T)] pSpec = (dir, T) :: pSpec := rfl

lemma append_assoc {pSpec₁ pSpec₂ pSpec₃ : ProtocolSpec} :
    append (append pSpec₁ pSpec₂) pSpec₃ = append pSpec₁ (append pSpec₂ pSpec₃) := by
  simp [append]

/-- Take the first `k` message of a protocol spec -/
def take (k : ℕ) (pSpec : ProtocolSpec) (h : k ≤ pSpec.length) : ProtocolSpec :=
  List.takeChecked k pSpec h

namespace Transcript

variable {pSpec pSpec₁ pSpec₂ : ProtocolSpec}

/-- Append two transcripts. Wrapper around `List.TProd.append` -/
def append {pSpec₁ pSpec₂ : ProtocolSpec}
    (tSpec₁ : Transcript pSpec₁) (tSpec₂ : Transcript pSpec₂) : Transcript (append pSpec₁ pSpec₂) :=
  List.TProd.append tSpec₁ tSpec₂

/-- The first half of a `Transcript` of an appended protocol spec. Wrapper around `List.TProd.fst`
-/
def fst {pSpec₁ pSpec₂ : ProtocolSpec} (tSpec : Transcript (pSpec₁ ++ pSpec₂)) :
    Transcript pSpec₁ := List.TProd.fst tSpec

/-- The second half of a `Transcript` of an appended protocol spec. Wrapper around `List.TProd.snd`
-/
def snd {pSpec₁ pSpec₂ : ProtocolSpec} (tSpec : Transcript (pSpec₁ ++ pSpec₂)) :
    Transcript pSpec₂ := List.TProd.snd tSpec

def cast {pSpec₁ pSpec₂ : ProtocolSpec} (h : pSpec₁ = pSpec₂)
    (tr : Transcript pSpec₁) : Transcript pSpec₂ := h ▸ tr

end Transcript

-- open OracleInterface in
-- def MessageOracleSpec (pSpec : ProtocolSpec) [∀ i, OracleInterface (pSpec.messageTypes.get i)] :
--     OracleSpec (Fin pSpec.messageTypes.length) :=
--   fun i => (Query (pSpec.messageTypes.get i), Response (pSpec.messageTypes.get i))

instance : ∀ i, OracleInterface ((messageTypes []).get i) := fun i => Fin.elim0 i

instance {α : Type} : ∀ i, OracleInterface ((messageTypes [(⟨.V_to_P, α⟩)]).get i) :=
  fun i => nomatch i

def appendOracleInterfaceMessage {pSpec pSpec' : ProtocolSpec}
    (Oₘ : ∀ i, OracleInterface (pSpec.messageTypes.get i))
    (Oₘ' : ∀ i, OracleInterface (pSpec'.messageTypes.get i)) :
    ∀ i, OracleInterface ((pSpec ++ pSpec').messageTypes.get i) :=
  match pSpec with
  | [] => Oₘ'
  | (.P_to_V, T) :: tl =>
    Fin.cons (Oₘ ⟨0, by simp [messageTypes]⟩)
      (appendOracleInterfaceMessage (fun i => Oₘ i.succ) Oₘ')
  | (.V_to_P, T) :: tl => by
    dsimp [messageTypes] at Oₘ ⊢
    exact appendOracleInterfaceMessage Oₘ Oₘ'

instance {pSpec pSpec' : ProtocolSpec} [Oₘ : ∀ i, OracleInterface (pSpec.messageTypes.get i)]
    [Oₘ' : ∀ i, OracleInterface (pSpec'.messageTypes.get i)] :
    ∀ i, OracleInterface ((pSpec ++ pSpec').messageTypes.get i) :=
  appendOracleInterfaceMessage Oₘ Oₘ'

def foldOracleInterfaceMessage (n : ℕ) (pSpec : Fin n → ProtocolSpec)
    (Oₘ : ∀ k, ∀ i, OracleInterface ((pSpec k).messageTypes.get i)) :
    ∀ i, OracleInterface
      ((Fin.foldl' n (fun i acc => append acc (pSpec i)) []).messageTypes.get i) :=
  match n with
  | 0 => fun i => Fin.elim0 i
  | m + 1 => by
    dsimp [messageTypes] at Oₘ ⊢
    refine appendOracleInterfaceMessage ?_ (Oₘ (Fin.last _))
    exact foldOracleInterfaceMessage m (pSpec ∘ Fin.castSucc) (fun k => Oₘ k.castSucc)

instance {n : ℕ} {pSpec : Fin n → ProtocolSpec}
    [Oₘ : ∀ k, ∀ i, OracleInterface ((pSpec k).messageTypes.get i)] :
    ∀ i, OracleInterface
      ((Fin.foldl' n (fun i acc => append acc (pSpec i)) []).messageTypes.get i) :=
  foldOracleInterfaceMessage n pSpec Oₘ

end ProtocolSpec

open ProtocolSpec

/-- The type of a prover interacting according to `pSpec`, with possible side effect defined by `m`,
  and output of type `Output`. -/
def InteractOutputProver (m : Type → Type) (Output : Type) (pSpec : ProtocolSpec) : Type :=
  match pSpec with
  | [] => Output
  | ⟨.P_to_V, MsgType⟩ :: tl => MsgType × m (InteractOutputProver m Output tl)
  | ⟨.V_to_P, ChalType⟩ :: tl => ChalType → m (InteractOutputProver m Output tl)

/-- Recreating the old prover - not very nice -/
structure StatefulInteractOutputProver (m : Type → Type u) (Output : Type)
    (pSpec : ProtocolSpec) where
  PrvState : Fin (pSpec.length + 1) → Type
  nextStep (i : Fin pSpec.length) (prvState : PrvState i.castSucc) :
    match (pSpec.get i).1 with
    | Direction.P_to_V => m ((pSpec.get i).2 × PrvState (i.succ))
    | Direction.V_to_P => m ((pSpec.get i).2 → PrvState (i.succ))
  output : PrvState (Fin.last pSpec.length) → Output

-- def StatefulInteractOutputProver (m : Type → Type u) (Output : Type)
--     (pSpec : ProtocolSpec) (States : List.TypeList.{1, 0} pSpec) : Type :=
--   match pSpec with
--   | [] => Output
--   | ⟨.P_to_V, MsgType⟩ :: tl => by
--     dsimp [List.TypeList] at States
--     exact (States.1 → (MsgType × m (StatefulInteractOutputProver m Output tl States.2)))
--   | ⟨.V_to_P, ChalType⟩ :: tl =>
--     ChalType → m (StatefulInteractOutputProver m Output tl StateList)

namespace InteractOutputProver

variable {m : Type → Type} {Output : Type} {pSpec : ProtocolSpec}

@[simp]
lemma nil_eq : InteractOutputProver m Output [] = Output := rfl

@[simp]
lemma cons_P_to_V_eq {MsgType : Type} :
    InteractOutputProver m Output (⟨.P_to_V, MsgType⟩ :: pSpec) =
    (MsgType × m (InteractOutputProver m Output pSpec)) := rfl

@[simp]
lemma cons_V_to_P_eq {ChalType : Type} :
    InteractOutputProver m Output (⟨.V_to_P, ChalType⟩ :: pSpec) =
    (ChalType → m (InteractOutputProver m Output pSpec)) := rfl

/-- Run an interactive prover given challenge values -/
def run [Monad m] {pSpec : ProtocolSpec}
    (prover : InteractOutputProver m Output pSpec) (challenges : Challenge pSpec) :
    m (Transcript pSpec × Output) := match pSpec with
  | [] => pure ((), prover)
  | ⟨.P_to_V, _⟩ :: _ => do
    let proverRest ← prover.2
    let outputRest ← run proverRest challenges
    return ((prover.1, outputRest.1), outputRest.2)
  | ⟨.V_to_P, _⟩ :: _ => do
    let proverRest ← prover challenges.1
    let outputRest ← run proverRest challenges.2
    return ((challenges.1, outputRest.1), outputRest.2)

end InteractOutputProver

/-- The type of an honest prover, which takes in a pair `(stmtIn, witIn)` and runs a prover
  interaction protocol. -/
def HonestProver (m : Type → Type) (StmtIn WitIn StmtOut WitOut : Type)
    (pSpec : ProtocolSpec) : Type :=
  StmtIn × WitIn → m (InteractOutputProver m (StmtOut × WitOut) pSpec)

namespace HonestProver

variable {m : Type → Type} {StmtIn WitIn StmtOut WitOut : Type} {pSpec : ProtocolSpec}

@[simp]
lemma nil_eq : HonestProver m StmtIn WitIn StmtOut WitOut [] =
  ((StmtIn × WitIn) → m (StmtOut × WitOut)) := rfl

@[simp]
lemma cons_P_to_V_eq {MsgType : Type} :
    HonestProver m StmtIn WitIn StmtOut WitOut (⟨.P_to_V, MsgType⟩ :: pSpec) =
    ((StmtIn × WitIn) → m (MsgType × m (InteractOutputProver m (StmtOut × WitOut) pSpec))) := by
  rfl

@[simp]
lemma cons_V_to_P_eq {ChalType : Type} :
    HonestProver m StmtIn WitIn StmtOut WitOut (⟨.V_to_P, ChalType⟩ :: pSpec) =
    ((StmtIn × WitIn) → m (ChalType → m (InteractOutputProver m (StmtOut × WitOut) pSpec))) := by
  rfl

protected def id [Pure m] : HonestProver m StmtIn WitIn StmtIn WitIn [] := pure

variable [Monad m]

/-- Sequentially compose an output-only prover with an IO prover
(where prev output match next input) -/
def comp' {Stmt₂ Wit₂ Stmt₃ Wit₃ : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    (prover₁ : InteractOutputProver m (Stmt₂ × Wit₂) pSpec₁)
    (prover₂ : HonestProver m Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) :
    m (InteractOutputProver m (Stmt₃ × Wit₃) (append pSpec₁ pSpec₂)) :=
  match pSpec₁ with
  | [] => prover₂ prover₁
  | ⟨.P_to_V, _⟩ :: _ => pure ⟨prover₁.1, do comp' (← prover₁.2) prover₂⟩
  | ⟨.V_to_P, _⟩ :: _ => pure fun chal => do comp' (← prover₁ chal) prover₂

/-- Sequentially compose two IO provers (where prev output match next input) -/
def comp {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    (prover₁ : HonestProver m Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (prover₂ : HonestProver m Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) :
    HonestProver m Stmt₁ Wit₁ Stmt₃ Wit₃ (append pSpec₁ pSpec₂) :=
  fun ctxIn => do comp' (← (prover₁ ctxIn)) prover₂

/-- Sequentially compose many provers in sequence (where prev output match next input)

What behavior do we want?
- `compNth (n := 0) ... = HonestProver.id`
- `compNth (n := 1) ... = comp HonestProver.id (prover 0)`
... -/
def compNth (n : ℕ) (Stmt : Fin (n + 1) → Type) (Wit : Fin (n + 1) → Type)
    (pSpec : Fin n → ProtocolSpec)
    (prover : (i : Fin n) →
      HonestProver m (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    HonestProver m (Stmt 0) (Wit 0) (Stmt (Fin.last n)) (Wit (Fin.last n))
      (Fin.foldl' n (fun i acc => append acc (pSpec i)) []) :=
  match n with
  | 0 => HonestProver.id
  | m + 1 => comp
      (compNth m
        (Stmt ∘ Fin.castSucc) (Wit ∘ Fin.castSucc) (pSpec ∘ Fin.castSucc)
        (fun i => prover (i.castSucc)))
      (prover (Fin.last m))

/-- Run an IO prover given an input and all challenge values, returning a transcript and output
-/
def run (prover : HonestProver m StmtIn WitIn StmtOut WitOut pSpec)
    (ctxIn : StmtIn × WitIn) (challenge : Challenge pSpec) :
    m (Transcript pSpec × StmtOut × WitOut) := do
  let proverInteractOutput ← prover ctxIn
  InteractOutputProver.run proverInteractOutput challenge

end HonestProver

/-- Just like prover but flipped direction.
May want to abstract this out into generic `two-party' computation
(enum would be `send/receive` instead of `P_to_V/V_to_P`) -/
def InteractOutputVerifier (m : Type → Type) (Output : Type) (pSpec : ProtocolSpec) : Type :=
  match pSpec with
  | [] => Output
  | ⟨.P_to_V, _⟩ :: tl => Output × m (InteractOutputVerifier m Output tl)
  | ⟨.V_to_P, _⟩ :: tl => Output → m (InteractOutputVerifier m Output tl)

/-- A public-coin verifier (rather, just the decision part, not the random sampling part) -/
def Verifier (m : Type → Type) (StmtIn StmtOut : Type) (pSpec : ProtocolSpec) : Type :=
  StmtIn → Transcript pSpec → m StmtOut

namespace Verifier

variable {m : Type → Type} {StmtIn StmtOut : Type} {pSpec : ProtocolSpec}

/-- The identity verifier -/
protected def id [Pure m] : Verifier m StmtIn StmtIn [] := fun x _ => pure x

/-- Sequentially compose two verifiers (where prev output match next input) -/
def comp [Monad m] {Stmt₁ Stmt₂ Stmt₃ : Type} {pSpec₁ pSpec₂ : ProtocolSpec}
    (verifier₁ : Verifier m Stmt₁ Stmt₂ pSpec₁)
    (verifier₂ : Verifier m Stmt₂ Stmt₃ pSpec₂) :
    Verifier m Stmt₁ Stmt₃ (append pSpec₁ pSpec₂) :=
  fun stmtIn transcript => do
    let stmtOut ← verifier₁ stmtIn transcript.fst
    verifier₂ stmtOut transcript.snd

/-- Sequentially compose many verifiers in sequence (where prev output match next input) -/
def compNth [Monad m] (n : ℕ) (Stmt : Fin (n + 1) → Type) (pSpec : Fin n → ProtocolSpec)
    (verifier : (i : Fin n) → Verifier m (Stmt i.castSucc) (Stmt i.succ) (pSpec i)) :
    Verifier m (Stmt 0) (Stmt (Fin.last n)) (Fin.foldl' n (fun i acc => append acc (pSpec i)) []) :=
  match n with
  | 0 => Verifier.id
  | m + 1 => Verifier.comp
    (compNth m (Stmt ∘ Fin.castSucc) (pSpec ∘ Fin.castSucc) (fun i => verifier i.castSucc))
    (verifier (Fin.last m))

end Verifier

open OracleInterface in
-- Here we need `OracleComp`. TODO: reconcile `m` which is unused here
-- (perhaps we can allow for different `m` for prover and verifier? also, different `m` per round?)
-- (needs very good monad lifting infrastructure)
structure OracleVerifier (_m : Type → Type)
    (StmtIn : Type) (OStmtIn : List Type) [∀ i, OracleInterface (OStmtIn.get i)]
    (StmtOut : Type) (OStmtOut : List Type) [∀ i, OracleInterface (OStmtOut.get i)]
    (pSpec : ProtocolSpec) [∀ i, OracleInterface (pSpec.messageTypes.get i)] where
  -- Return the output statement
  verify : StmtIn → pSpec.Challenge →
    OracleComp
      (toOracleSpecOfList pSpec.messageTypes ++ₒ toOracleSpecOfList OStmtIn) StmtOut

  -- Return the output oracle statement implicitly, via specifying an oracle simulation
  simulate : StmtIn → pSpec.Challenge →
    QueryImpl (toOracleSpecOfList OStmtOut)
      (OracleComp (toOracleSpecOfList OStmtIn ++ₒ toOracleSpecOfList pSpec.messageTypes))

open OracleSpec OracleQuery in
def QueryImpl.inl {ι ι' : Type u} {spec : OracleSpec ι} {spec' : OracleSpec ι'} :
    QueryImpl spec (OracleComp (spec ++ₒ spec')) where
  impl | query i t => query (spec := spec ++ₒ spec') (Sum.inl i) t

open OracleSpec OracleQuery in
def QueryImpl.inr {ι ι' : Type u} {spec : OracleSpec ι} {spec' : OracleSpec ι'} :
    QueryImpl spec (OracleComp (spec' ++ₒ spec)) where
  impl | query i t => query (spec := spec' ++ₒ spec) (Sum.inr i) t

namespace OracleVerifier

variable {m : Type → Type}
    {StmtIn : Type} {OStmtIn : List Type} [∀ i, OracleInterface (OStmtIn.get i)]
    {StmtOut : Type} {OStmtOut : List Type} [∀ i, OracleInterface (OStmtOut.get i)]
    {pSpec : ProtocolSpec}

/-- The identity oracle verifier -/
protected def id [Pure m] (StmtIn : Type)
    (OStmtIn : List Type) [∀ i, OracleInterface (OStmtIn.get i)] :
    OracleVerifier m StmtIn OStmtIn StmtIn OStmtIn [] where
  verify := fun x _ => pure x
  simulate := fun _ _ => QueryImpl.inl

/-- Sequential composition of two oracle verifiers, where oracle interfaces are explicit -/
def comp' [Monad m] {Stmt₁ Stmt₂ Stmt₃ : Type}
    {OStmt₁ OStmt₂ OStmt₃ : List Type}
    {Oₛ₁ : ∀ i, OracleInterface (OStmt₁.get i)}
    {Oₛ₂ : ∀ i, OracleInterface (OStmt₂.get i)}
    {Oₛ₃ : ∀ i, OracleInterface (OStmt₃.get i)}
    {pSpec₁ pSpec₂ : ProtocolSpec}
    {Oₘ₁ : ∀ i, OracleInterface (pSpec₁.messageTypes.get i)}
    {Oₘ₂ : ∀ i, OracleInterface (pSpec₂.messageTypes.get i)}
    (verifier₁ : OracleVerifier m Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (verifier₂ : OracleVerifier m Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
    OracleVerifier m Stmt₁ OStmt₁ Stmt₃ OStmt₃ (pSpec₁ ++ pSpec₂) :=
  sorry

/-- Sequential composition of two oracle verifiers -/
def comp [Monad m] {Stmt₁ Stmt₂ Stmt₃ : Type}
    {OStmt₁ OStmt₂ OStmt₃ : List Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁.get i)]
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂.get i)]
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃.get i)]
    {pSpec₁ pSpec₂ : ProtocolSpec}
    [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.messageTypes.get i)]
    [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.messageTypes.get i)]
    (verifier₁ : OracleVerifier m Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (verifier₂ : OracleVerifier m Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
    OracleVerifier m Stmt₁ OStmt₁ Stmt₃ OStmt₃ (pSpec₁ ++ pSpec₂) :=
  comp' verifier₁ verifier₂

/-- Sequential composition of many oracle verifiers in sequence. Version with explicit oracle
  interfaces. -/
def compNth' [Monad m] (n : ℕ) (Stmt : Fin (n + 1) → Type)
    (OStmt : Fin (n + 1) → List Type) {Oₛ : ∀ k, ∀ i, OracleInterface ((OStmt k).get i)}
    (pSpec : Fin n → ProtocolSpec) {Oₘ : ∀ k, ∀ i, OracleInterface ((pSpec k).messageTypes.get i)}
    (verifier : (i : Fin n) → OracleVerifier m (Stmt i.castSucc) (OStmt i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (pSpec i)) :
    OracleVerifier m (Stmt 0) (OStmt 0) (Stmt (Fin.last n)) (OStmt (Fin.last n))
      (Fin.foldl' n (fun i acc => append acc (pSpec i)) []) :=
  match n with
  | 0 => OracleVerifier.id (Stmt 0) (OStmt 0)
  | n + 1 => OracleVerifier.comp'
    (compNth' n (Stmt ∘ Fin.castSucc) (fun i => OStmt i.castSucc) (pSpec ∘ Fin.castSucc)
      (fun i => verifier i.castSucc))
    (verifier (Fin.last n))

def compNth [Monad m] (n : ℕ) (Stmt : Fin (n + 1) → Type)
    (OStmt : Fin (n + 1) → List Type) [Oₛ : ∀ k, ∀ i, OracleInterface ((OStmt k).get i)]
    (pSpec : Fin n → ProtocolSpec) [Oₘ : ∀ k, ∀ i, OracleInterface ((pSpec k).messageTypes.get i)]
    (verifier : (i : Fin n) → OracleVerifier m (Stmt i.castSucc) (OStmt i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (pSpec i)) :
    OracleVerifier m (Stmt 0) (OStmt 0) (Stmt (Fin.last n)) (OStmt (Fin.last n))
      (Fin.foldl' n (fun i acc => append acc (pSpec i)) []) :=
  compNth' n Stmt OStmt pSpec verifier

end OracleVerifier

variable {m : Type → Type} [Monad m] [HasEvalDist m] {StmtIn StmtOut : Type} {pSpec : ProtocolSpec}

/-- A (deterministic) state function for a verifier, with respect to input language `langIn` and
  output language `langOut`. This is used to define round-by-round soundness. -/
structure StateFunction
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier m StmtIn StmtOut pSpec)
    where
  toFun : (m : Fin (pSpec.length + 1)) → StmtIn → PartialTranscript pSpec m → Prop
  /-- For all input statement not in the language, the state function is false for that statement
    and the empty transcript -/
  toFun_empty : ∀ stmt, stmt ∈ langIn ↔ toFun 0 stmt ()
  /-- If the state function is false for a partial transcript, and the next message is from the
    prover to the verifier, then the state function is also false for the new partial transcript
    regardless of the message -/
  toFun_next : ∀ m, (pSpec.get m).fst = .P_to_V →
    ∀ stmt tr, ¬ toFun m.castSucc stmt tr →
    ∀ msg, ¬ toFun m.succ stmt (tr.concat msg)
  /-- If the state function is false for a full transcript, the verifier will not output a statement
    in the output language -/
  toFun_full : ∀ stmt tr, ¬ toFun (.last _) stmt tr →
    Pr[(· ∈ langOut) | verifier stmt tr.toFull] = 0
