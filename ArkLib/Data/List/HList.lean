/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Matrix.DMatrix
import Mathlib.Data.Fin.Tuple.Curry
import Mathlib.Tactic

/-!
  # Heterogeneous Lists

  We define `HList` as a synonym for `List (Σ α : Type u, α)`, namely a list of types together with
  a value.

  We note some other implementations of `HList`:
  - [Soup](https://github.com/crabbo-rave/Soup/tree/master)
  - Part of Certified Programming with Dependent Types (it's in Coq, but can be translated to Lean)

  Our choice of definition is so that we can directly rely on the existing API for `List`.
-/

universe u v

/-- Heterogeneous list -/
abbrev HList := List (Σ α : Type u, α)

namespace HList

def nil : HList := []

def cons (x : Σ α : Type u, α) (xs : HList) : HList := x :: xs

syntax (name := hlist) "[" term,* "]ₕ" : term
macro_rules (kind := hlist)
  | `([]ₕ) => `(HList.nil)
  | `([$x]ₕ) => `(HList.cons $x HList.nil)
  | `([$x, $xs,*]ₕ) => `(HList.cons $x [$xs,*]ₕ)

/- HList.cons notation -/
infixr:67 " ::ₕ " => HList.cons

variable {x : (α : Type u) × α} {xs : HList}

@[simp]
lemma cons_eq_List.cons : x ::ₕ xs = x :: xs := rfl

@[simp]
lemma length_nil : nil.length = 0 := rfl

@[simp]
lemma length_cons (x : Σ α : Type u, α) (xs : HList) : (x ::ₕ xs).length = xs.length + 1 := rfl

/-- Returns the types of the elements in the `HList` -/
def getTypes : HList → List (Type u) := List.map (fun x => x.1)

@[simp]
lemma getTypes_nil : getTypes [] = [] := rfl

@[simp]
lemma getTypes_cons (x : Σ α : Type u, α) (xs : HList) :
    getTypes (x :: xs) = x.1 :: xs.getTypes := rfl

@[simp]
lemma getTypes_hcons (x : Σ α : Type u, α) (xs : HList) :
    (x ::ₕ xs).getTypes = x.1 :: xs.getTypes := rfl

@[simp]
lemma length_getTypes (l : HList) : l.getTypes.length = l.length := by
  induction l with
  | nil => simp
  | cons _ xs ih => simp [ih]

@[simp]
lemma getTypes_eq_get_fst (l : HList) (i : Fin l.length) : l.getTypes[i] = l[i].1 := by
  induction l with
  | nil => simp at i; exact isEmptyElim i
  | cons x xs ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · aesop


/-- Get the value of the element at index `i`, of type `l[i].1` -/
def getValue (l : HList) (i : Fin l.length) := l[i].2

end HList

variable {α : Type u} {n : ℕ}

@[simp]
lemma List.get_nil (i : Fin 0) (a : α) : [].get i = a := by exact isEmptyElim i

/-- Dependent vectors
-/
def DVec {m : Type v} (α : m → Type u) : Type (max u v) := ∀ i, α i


/-- Convert a `HList` to a `DVec` -/
def HList.toDVec (l : HList) : DVec (m := Fin l.length) (fun i => l[i].1) := fun i => l[i].2

/-- Create an `HList` from a `DVec` -/
def HList.ofDVec {α : Fin n → Type u} (l : DVec (m := Fin n) α) :
    HList := (List.finRange n).map fun i => ⟨α i, l i⟩

-- /-- Convert a `DVec` to an `HList` -/
-- def DVec.toHList (l : DVec (m := Fin n) α) : HList := (List.finRange n).map fun i => ⟨α i, l i⟩

-- theorem DVec.toHList_getTypes (l : DVec (m := Fin n) α) :
--     l.toHList.getTypes = List.ofFn α := by aesop


/-- Equivalent between `HList.getValue` and `HList.toDVec` -/
lemma HList.toDVec_eq_getValue (l : HList) (i : Fin l.length) : l.toDVec i = l.getValue i := rfl


/-

Other candidate implementations of `HList`:

-- This is a port from [Soup](https://github.com/crabbo-rave/Soup/tree/master)

inductive HList : List (Type u) → Type (u + 1) where
  | nil : HList []
  | cons {α : Type u} (x : α) {αs : List (Type u)} (xs : HList αs) : HList (α :: αs)

syntax (name := hlist) "[" term,* "]ₕ" : term
macro_rules (kind := hlist)
  | `([]ₕ) => `(HList.nil)
  | `([$x]ₕ) => `(HList.cons $x HList.nil)
  | `([$x, $xs,*]ₕ) => `(HList.cons $x [$xs,*]ₕ)

/- HList.cons notation -/
infixr:67 " ::ₕ " => HList.cons


namespace HList

/-- Returns the first element of a HList -/
def head {α : Type u} {αs : List (Type u)} : HList (α :: αs) → α
  | x ::ₕ _ => x

/-- Returns a HList of all the elements besides the first -/
def tail {α : Type u} {αs : List (Type u)} : HList (α :: αs) → HList αs
  | _ ::ₕ xs => xs

/-- Returns the length of a HList -/
def length {αs : List (Type u)} (_ : HList αs) := αs.length

/-- Returns the nth element of a HList -/
@[reducible]
def get {αs : List (Type u)} : HList αs → (n : Fin αs.length) → αs.get n
  | x ::ₕ _, ⟨0, _⟩ => x
  | _ ::ₕ xs, ⟨n+1, h⟩ => xs.get ⟨n, Nat.lt_of_succ_lt_succ h⟩

def getTypes {αs : List Type} (_ : HList αs) : List Type := αs

/--
`O(|join L|)`. `join L` concatenates all the lists in `L` into one list.
* `join [[a], [], [b, c], [d, e, f]] = [a, b, c, d, e, f]`
-/
-- def join {αs : List (Type u)} {βs : αs → List (Type v)} : HList (List (HList βs)) → HList αs
--   | []      => []
--   | a :: as => a ++ join as

@[simp] theorem join_nil : List.join ([] : List (List α)) = [] := rfl
@[simp] theorem join_cons : (l :: ls).join = l ++ ls.join := rfl


section Repr

class HListRepr (α : Type _) where
  repr: α → Std.Format

instance : HListRepr (HList []) where
  repr := fun _ => ""

instance [Repr α] (αs : List Type) [HListRepr (HList αs)] : HListRepr (HList (α :: αs)) where
  repr
  | HList.cons x xs =>
    match xs with
    | HList.nil => reprPrec x 0
    | HList.cons _ _ => reprPrec x 0 ++ ", " ++ HListRepr.repr xs

/-- Repr instance for HLists -/
instance (αs : List Type) [HListRepr (HList αs)] : Repr (HList αs) where
  reprPrec
  | v, _ => "[" ++ HListRepr.repr v ++ "]"

class HListString (α : Type _) where
  toString : α → String

instance : HListString (HList []) where
  toString
  | HList.nil => ""

instance [ToString α] (αs : List Type) [HListString (HList αs)] :
    HListString (HList (α :: αs)) where
  toString
  | HList.cons x xs =>
    match xs with
    | HList.nil => toString x
    | HList.cons _ _ => toString x ++ ", " ++ HListString.toString xs

/-- ToString instance for HLists -/
instance (αs : List Type) [HListString (HList αs)] : ToString (HList αs) where
  toString : HList αs → String
  | t => "[" ++ HListString.toString t ++ "]"

end Repr

def test : HList [Nat, String, Nat] :=
  HList.cons 1 (HList.cons "bad" (HList.cons 3 HList.nil))

#eval test


-- def mapNthNoMetaEval : (n : Fin αs.length) → ((αs.get n) → β) → HList αs → HList (αs.repla n β)
--   | ⟨0, _⟩, f, a::as => (f a)::as
--   | ⟨n+1, h⟩, f, a::as => a::(as.mapNthNoMetaEval ⟨n, Nat.lt_of_succ_lt_succ h⟩ f)

-- def mapNth (n : Fin' αs.length) (f : (αs.get' n) → β) (h : HList αs) :
--     HList (αs.replaceAt n β) :=
--   let typeSig : List Type := αs.replaceAt n β
--   the (HList typeSig) (h.mapNthNoMetaEval n f)

end HList

-- The indexed HList below is equivalent to `List.TProd`

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

-/
