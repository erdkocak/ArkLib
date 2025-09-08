import Mathlib
import ArkLib.OracleReduction.OracleInterface
import ArkLib.OracleReduction.Prelude
import ArkLib.Data.Fin.Fold

universe u v

/- Testing out `TProd` and its properties -/

inductive HList {ι : Type v} (α : ι → Type u) : List ι → Type (max u v)
  | nil : HList α []
  | cons {i : ι} {is : List ι} : α i → HList α is → HList α (i :: is)

namespace HList

variable {ι : Type v} (α : ι → Type u)

inductive member (a : ι) : List ι → Type v where
  | first (ls : List ι) : member a (a :: ls)
  | next (i : ι) (ls : List ι) : member a ls → member a (i :: ls)

-- The length of an `HList α ls` is just the length of its index list `ls`.
def length (ls : List ι) (_ : HList α ls) : Nat := ls.length

def get {ls : List ι} (hs : HList α ls) {i : ι} (h : member i ls) : α i :=
  match hs, h with
  | nil, h => nomatch h
  | cons a _, member.first _ => a
  | cons _ as, member.next _ _ h' => get as h'

def toTProd : (ls : List ι) → (hs : HList α ls) → List.TProd α ls
  | [], _ => PUnit.unit
  | _ :: is, cons a as => (a, toTProd is as)

@[simp]
lemma toTProd_nil {hs : HList α []} : toTProd α [] hs = PUnit.unit := rfl

@[simp]
lemma toTProd_cons {i : ι} {is : List ι} {a : α i} {as : HList α is} :
    toTProd α (i :: is) (HList.cons a as) = (a, toTProd α is as) := rfl

/-- Convert a `List.TProd` back into an `HList`. -/
def ofTProd : (ls : List ι) → List.TProd α ls → HList α ls
  | [], _ => HList.nil
  | _ :: is, (a, as) => HList.cons a (ofTProd is as)

@[simp]
lemma ofTProd_nil : ofTProd α [] PUnit.unit = HList.nil := rfl

@[simp]
lemma ofTProd_cons {i : ι} {is : List ι} {a : α i} {as : List.TProd α is} :
    ofTProd α (i :: is) (a, as) = HList.cons a (ofTProd α is as) := rfl

@[simp]
theorem toTProd_ofTProd (ls : List ι) (t : List.TProd α ls) :
      HList.toTProd α ls (ofTProd α ls t) = t := by
  induction ls with
  | nil => cases t; rfl
  | cons i is ih => cases t; simp [ih]

@[simp]
theorem ofTProd_toTProd (ls : List ι) (hs : HList α ls) :
      ofTProd α ls (HList.toTProd α ls hs) = hs := by
  induction ls with
  | nil => cases hs; rfl
  | cons i is ih => cases hs; simp [ih]

/-- `HList α ls` is equivalent to `List.TProd α ls`. -/
def equivTProd (ls : List ι) : HList α ls ≃ List.TProd α ls where
  toFun := HList.toTProd α ls
  invFun := ofTProd α ls
  left_inv := by intro _; simp [ofTProd_toTProd]
  right_inv := by intro _; simp [toTProd_ofTProd]

end HList

#check List.TProd

def testTProdthm : List.TProd (fun (i : ℕ) => Fin i) [1, 2, 3] = Nat := by
  unfold List.TProd
  dsimp
  sorry

#print List.append

#print List.get

def testTProd : List.TProd (fun (i : ℕ) => Fin i) [1, 2, 3] :=
  ⟨0, 1, 2, ()⟩

def List.TProd.get {ι : Type u} {α : ι → Type v} {l : List ι}
    (t : l.TProd α) (n : Nat) {i : ι} (hi : l[n]? = some i) : α i :=
  match l, t, n, hi with
  | _ :: _, (a, _), 0, rfl => a
  | _ :: _, (_, as), n + 1, hi => List.TProd.get as n hi

example {ι : Type*} {α : ι → Type*} {v : List.TProd α []} : v = PUnit.unit := rfl

namespace List

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
lemma cons_eq {i : ι} {is : List ι} : TProd α (i :: is) = ((α i) × TProd α is) := rfl

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
  match l, t with
  | [], _ => (a, PUnit.unit)
  | _ :: _, (a₀, as) => (a₀, concat as a)

@[simp] theorem concat_nil {i : ι} (a : α i) :
    concat (α:=α) (l:=[]) (t:=PUnit.unit) a = (a, PUnit.unit) := rfl

@[simp]
theorem concat_cons {i : ι} {is : List ι} (a₀ : α i) (as : TProd α is)
    {j : ι} (a : α j) :
    concat (α:=α) (l:=i :: is) (t:=(a₀, as)) a = (a₀, concat (α:=α) (l:=is) (t:=as) a) := rfl

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
      | _ a₀ as =>
        simpa [concat, getMember] using ih as

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
      | _ a₀ as =>
        simpa [concat, append] using congrArg (Prod.mk a₀) (ih as)

end TProd
end List

def Direction.swap : Direction → Direction
  | Direction.P_to_V => Direction.V_to_P
  | Direction.V_to_P => Direction.P_to_V

@[reducible]
def ProtocolSpec := List (Direction × Type)

namespace ProtocolSpec

/-- Flip the direction of each element in the protocol spec -/
def flipDir (pSpec : ProtocolSpec) : ProtocolSpec :=
  pSpec.map (fun x => (x.fst.swap, x.snd))

-- def «Type» : (pSpec : ProtocolSpec) → Type
--   | [] => Unit
--   | (_, t) :: ps => t × «Type» ps

-- def MessageTypeList (pSpec : ProtocolSpec) : List Type :=
--   pSpec.filterMap (fun ⟨dir, T⟩ => match dir with
--   | Direction.P_to_V => some T
--   | Direction.V_to_P => none)

-- def ChallengeTypeList (pSpec : ProtocolSpec) : List Type :=
--   pSpec.filterMap (fun ⟨dir, T⟩ => match dir with
--   | Direction.P_to_V => none
--   | Direction.V_to_P => some T)

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
def take (k : Nat) (pSpec : ProtocolSpec) : ProtocolSpec := List.take k pSpec

namespace Transcript

variable {pSpec pSpec₁ pSpec₂ : ProtocolSpec}

/-- Append two transcripts. Wrapper around `List.TProd.append` -/
def append {pSpec₁ pSpec₂ : ProtocolSpec}
    (tSpec₁ : Transcript pSpec₁) (tSpec₂ : Transcript pSpec₂) : Transcript (append pSpec₁ pSpec₂) :=
  List.TProd.append tSpec₁ tSpec₂

def cast {pSpec₁ pSpec₂ : ProtocolSpec} (h : pSpec₁ = pSpec₂)
    (tr : Transcript pSpec₁) : Transcript pSpec₂ := h ▸ tr

end Transcript

end ProtocolSpec

open ProtocolSpec

-- structure Prover (pSpec : ProtocolSpec) (StmtIn WitIn StmtOut WitOut : Type) where
--   PrvState : Fin (pSpec.length + 1) → Type

/-- The type of a prover interacting according to `pSpec`, with possible side effect defined by `m`,
  and output of type `Output`. -/
def InteractOutputProver (m : Type → Type) (Output : Type) (pSpec : ProtocolSpec) : Type :=
  match pSpec with
  | [] => Output
  | ⟨.P_to_V, MsgType⟩ :: tl => MsgType × m (InteractOutputProver m Output tl)
  | ⟨.V_to_P, ChalType⟩ :: tl => ChalType → m (InteractOutputProver m Output tl)

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

protected def id [Pure m] : Verifier m StmtIn StmtIn [] := fun x _ => pure x

end Verifier

-- Here we need `OracleComp`
def OracleVerifier (m : Type → Type) (StmtIn StmtOut : Type)
    (pSpec : ProtocolSpec) [∀ i, OracleInterface (pSpec.messageTypes.get i)] : Type :=
  StmtIn → Transcript pSpec → m StmtOut
