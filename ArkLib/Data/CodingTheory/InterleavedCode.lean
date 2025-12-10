/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import ArkLib.Data.Fin.Basic
import ArkLib.Data.CodingTheory.Prelims
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ENat.Lattice
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.Qify
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Data.NNReal.Defs

noncomputable section

/-!
  Definition of an interleaved code of a linear code over a semiring.
  Definition of distances for interleaved codes and statement for the relation between the minimal
  distance of an interleaved code and its underlying linear code.
  Statements of proximity results for Reed Solomon codes (`Lemma 4.3`, `Lemma 4.4` and `Lemma 4.5`
   from `[AHIV22]` : `Ligero: Lightweight Sublinear Arguments Without a Trusted Setup`
   by `S. Ames, C. Hazay, Y. Ishai, M. Venkitasubramaniam`.

  -- TODO: use new APIs for AHIV22 & bring its statements to another file
-/

variable {F : Type*} [Semiring F]
         {κ ι : Type*} [Fintype κ] [Fintype ι]
         {LC : LinearCode ι F}

abbrev MatrixSubmodule.{u, v, w} (κ : Type u) [Fintype κ] (ι : Type v) [Fintype ι]
                                 (F : Type w) [Semiring F] : Type (max u v w) :=
  Submodule F (Matrix κ ι F)

/-- The data needed to construct an interleaved code.
-/
structure InterleavedCode (κ ι : Type*) [Fintype κ] [Fintype ι] (F : Type*) [Semiring F] where
  MF : MatrixSubmodule κ ι F
  LC : LinearCode ι F

namespace InterleavedCode

/-- The condition making the `InterleavedCode` structure an interleaved code.
-/
def isInterleaved (IC : InterleavedCode κ ι F) :=
  ∀ V ∈ IC.MF, ∀ i, V i ∈ IC.LC

def LawfulInterleavedCode (κ : Type*) [Fintype κ] (ι : Type*) [Fintype ι]
                          (F : Type*) [Semiring F] :=
  { IC : InterleavedCode κ ι F // IC.isInterleaved }

/-- The submodule of the module of matrices whose rows belong to a linear code.
-/
def matrixSubmoduleOfLinearCode (κ : Type*) [Fintype κ]
                                (LC : LinearCode ι F) : MatrixSubmodule κ ι F :=
  Submodule.span F { V | ∀ i, V i ∈ LC }

def codeOfLinearCode (κ : Type*) [Fintype κ] (LC : LinearCode ι F) : InterleavedCode κ ι F :=
  { MF := matrixSubmoduleOfLinearCode κ LC, LC := LC }

/-- The module of matrices whose rows belong to a linear code is in fact an interleaved code.
-/
lemma isInterleaved_codeOfLinearCode : (codeOfLinearCode κ LC).isInterleaved := by
  intro V hv
  simp_all [codeOfLinearCode, matrixSubmoduleOfLinearCode]
  induction hv using Submodule.span_induction <;> intro i
  case mem M hm => exact hm i
  case zero => exact Submodule.zero_mem LC
  case add M N hm hn him hin =>
    apply Submodule.add_mem
    · exact him i
    · exact hin i
  case smul a M hm him =>
    apply Submodule.smul_mem
    ·  exact him i

def lawfulInterleavedCodeOfLinearCode (κ : Type*) [Fintype κ] (LC : LinearCode ι F) :
  LawfulInterleavedCode κ ι F := ⟨codeOfLinearCode κ LC, isInterleaved_codeOfLinearCode⟩

/-- Distance between codewords of an interleaved code.
-/
def distCodewords [DecidableEq F] (U V : Matrix κ ι F) : ℕ :=
  (Matrix.neqCols U V).card

/-- `Δ(U,V)` is the distance between codewords `U` and `V` of a `κ`-interleaved code `IC`.
-/
notation "Δ(" U "," V ")" => distCodewords U V

/-- Minimal distance of an interleaved code.
-/
def minDist [DecidableEq F] (IC : MatrixSubmodule κ ι F) : ℕ :=
  sInf { d : ℕ | ∃ U ∈ IC, ∃ V ∈ IC, distCodewords U V = d }

/-- `Δ IC` is the min distance of an interleaved code `IC`.
-/
notation "Δ" IC => minDist IC

/-- Distance from a matrix to the closest word in an interleaved code.
-/
def distToCode [DecidableEq F] (U : Matrix κ ι F) (IC : MatrixSubmodule κ ι F) : ℕ :=
 sInf { d : ℕ | ∃ V ∈ IC, distCodewords U V = d }

/-- `Δ(U,C')` denotes distance between a `κ x ι` matrix `U` and `κ`-interleaved code `IC`.
-/
notation "Δ(" U "," IC ")" => distToCode U IC

/-- Relative distance between codewords of an interleaved code.
-/
def relDistCodewords [DecidableEq F] (U V : Matrix κ ι F) : ℝ :=
  (Matrix.neqCols U V).card / Fintype.card ι

/-- The list of codewords of `IC` `r`-close to `U`, with respect to relative distance of
interleaved codes.
-/
def relHammingBallInterleavedCode [DecidableEq F] (U : Matrix κ ι F)
  (IC : MatrixSubmodule κ ι F) (r : ℝ) :=
    {V | V ∈ IC ∧ relDistCodewords U V < r}

/-- `Λᵢ(U, IC, r)` denotes the list of codewords of IC `r`-close to `U`.
-/
notation "Λᵢ(" U "," IC "," r ")" => relHammingBallInterleavedCode U IC r

/-- The minimal distance of an interleaved code is the same as the minimal distance of its
underlying linear code.
-/
lemma minDist_eq_minDist [DecidableEq F] {IC : LawfulInterleavedCode κ ι F} :
  Code.minDist (IC.1.LC : Set (ι → F)) = minDist IC.1.MF := by sorry

end InterleavedCode

/-!
  ## ModuleCode Interleaved Code Infrastructure

  This section provides infrastructure for working with interleaved codes derived from `ModuleCode`.
  It includes helper functions for transposing and extracting rows from interleaved codewords, as
  well as instances and lemmas for converting `ModuleCode` to interleaved codes.

Different namings:
1. Word: a vector (ι → A)
2. Codeword: a vector (ι → A) that belongs to the base module code MC
3. Word stack: Matrix (ι → A) where each row is a word
3. Codeword stack: Matrix (κ → ι → A) where each row is a codeword of the base module code MC

In the interleaved code MC^⋈ κ realm, each column is a symbol, i.e. (κ → A), each row is a codeword
  of the base module code MC.

5. Interleaved Word: a matrix (ι → (κ → A)).
6. Interleaved Codeword: a matrix (ι → (κ → A)), where each tranposed row (ι → A) is a codeword
  of the base module code MC.
-/

section InterleavedCodeDefinitions
variable (F : Type*) [Semiring F]
variable (A : Type*) [AddCommMonoid A] [Module F A]
variable (κ ι : Type*) [Fintype κ] [Fintype ι]
variable (MC : ModuleCode ι F A)
variable (C : Set (ι → A))

namespace Code

/-- A word is a vector (ι → A) -/
@[simp]
abbrev Word := ι → A

/-- A codeword is a vector (ι → A) that belongs to the base module code MC -/
@[simp]
abbrev Codeword := MC

@[simp]
abbrev InterleavedSymbol := κ → A

/-- A word stack is a (row-wise) matrix (κ → ι → A) where each ROW is a word -/
@[simp]
abbrev WordStack := Matrix κ ι A

@[simp]
def WordStack.getRowWord {A : Type*} {κ : Type*} {ι : Type*} (u : WordStack A κ ι)
    (k : κ) : Word A ι := u k

@[simp]
def WordStack.getSymbol {A : Type*} {κ : Type*} {ι : Type*} (u : WordStack A κ ι)
    (i : ι) : InterleavedSymbol A κ := u.transpose i

/-- An interleaved word is a (column-wise) matrix (ι → (κ → A)) where each ROW is a word, each
  column i is a symbol (κ → A) for the interleaved code MC^⋈ κ. -/
@[simp]
abbrev InterleavedWord := Matrix ι κ A

@[simp]
def InterleavedWord.getRowWord {A : Type*} {κ : Type*} {ι : Type*}
    (v : InterleavedWord A κ ι) (k : κ) : Word A ι := v.transpose k

@[simp]
def InterleavedWord.getSymbol {A : Type*} {κ : Type*} {ι : Type*}
    (v : InterleavedWord A κ ι) (i : ι) : InterleavedSymbol A κ := v i

/-- The set of interleaved words where each row belongs to a code C.
    This is a generic version that works for any code represented as a Set. -/
@[simp]
def interleavedCodeSet {A : Type*} {κ ι : Type*}
    (C : Set (ι → A)) : Set (Matrix ι κ A) :=
  { V : Matrix ι κ A | ∀ k : κ, V.transpose k ∈ C }

/-- If C is finite and membership is decidable, then interleavedCodeSet C is finite. -/
@[simp]
instance interleavedCodeSet_fintype {A : Type*} {κ ι : Type*}
    [Fintype κ] [Fintype ι] [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) :
    Fintype (interleavedCodeSet (κ := κ) (ι := ι) C) := by
  exact Fintype.ofFinite (interleavedCodeSet C)

/-- Interleaved code submodule of any `ModuleCode`, where each row belongs to the code. -/
@[simp]
instance ModuleCode.moduleInterleavedCode : ModuleCode ι F (InterleavedSymbol A κ) := {
  -- Simple condition wrapping over Matrix
  carrier := interleavedCodeSet (C := (MC : Set (ι → A)))
  add_mem' hU hV i := MC.add_mem (hU i) (hV i)
  zero_mem' _ := MC.zero_mem
  smul_mem' a _ hV i := MC.smul_mem a (hV i)
}

-- TODO: lift these to CodeInterleavable
omit [Fintype κ] [Fintype ι] [AddCommMonoid A] in
@[simp]
lemma mem_interleavedCode_iff (v : InterleavedWord A κ ι) : -- column-wise matrix
    v ∈ interleavedCodeSet (C := C) ↔ ∀ k, InterleavedWord.getRowWord v k ∈ C := by rfl

omit [Fintype κ] [Fintype ι] in
lemma mem_moduleInterleavedCode_iff (v : InterleavedWord A κ ι) :
    v ∈ ModuleCode.moduleInterleavedCode (F := F) (A := A) (κ := κ) (ι := ι) (MC := MC)
    ↔ ∀ k, InterleavedWord.getRowWord v k ∈ MC := by exact Eq.to_iff rfl

@[simp]
def codewordStackSet {A : Type*} {κ ι : Type*} (C : Set (ι → A)) : Set (WordStack A κ ι) :=
  { V : WordStack A κ ι | ∀ k, V.getRowWord k ∈ C }

@[simp]
instance ModuleCode.codewordStackSubmodule : Submodule F (WordStack A κ ι) := {
  -- Simple condition wrapping over Matrix
  carrier := codewordStackSet (C := (MC : Set (ι → A)))
  add_mem' hU hV i := MC.add_mem (hU i) (hV i)
  zero_mem' _ := MC.zero_mem
  smul_mem' a _ hV i := MC.smul_mem a (hV i)
}

omit [Fintype κ] [Fintype ι] in
lemma codewordStackSubmodule_eq_codewordStackSet (MC : ModuleCode ι F A) :
    ((ModuleCode.codewordStackSubmodule (MC := MC) F A κ ι) : Set (WordStack A κ ι))
      = codewordStackSet (MC : Set (ι → A)) := rfl

instance instMembershipWordStackCodewordStackSet : Membership (α := WordStack A κ ι)
  (γ := codewordStackSet (κ := κ) (C := C)) where
  mem u := by exact fun a ↦ PEmpty.{0}

instance instMembershipInterleavedWordInterleavedCodeSet :
  Membership (InterleavedWord A κ ι) (interleavedCodeSet (κ := κ) (C := C)) where
  mem u := by exact fun a ↦ PEmpty.{0}

omit [Fintype κ] [Fintype ι] [AddCommMonoid A] in
@[simp]
lemma mem_codewordStack_iff (u : WordStack A κ ι) : -- row-wise matrix
    u ∈ codewordStackSet (κ := κ) (C := C) ↔ ∀ k, u.getRowWord k ∈ C := by rfl

omit [Fintype κ] [Fintype ι] in
@[simp]
lemma mem_moduleCodewordStack_iff (u : WordStack A κ ι) : -- might rename this
    u ∈ ModuleCode.codewordStackSubmodule (F := F) (A := A) (κ := κ) (ι := ι) (MC := MC)
    ↔ ∀ k, u.getRowWord k ∈ MC := by exact Eq.to_iff rfl

/-- An interleaved codeword is a (column-wise) matrix (ι → (κ → A)) where each ROW is a codeword
  of the base module code MC. -/
@[simp]
abbrev InterleavedCodeword := interleavedCodeSet (κ := κ) (C := C)

/-- A codeword stack is a (row-wise) matrix (κ → ι → A) where each ROW is a codeword of MC. -/
@[simp]
abbrev CodewordStack := codewordStackSet (κ := κ) (C := C)

-- TODO: mem of Module interleaved code, Module codeword stack

@[simp]
def interleaveWordStack {A : Type*} {κ ι : Type*} (u : WordStack A κ ι) : InterleavedWord A κ ι
    := u.transpose

/-- Interleave a codeword stack into an interleaved codeword. -/
@[simp]
def interleaveCodewordStack (u : CodewordStack A κ ι C) : InterleavedCodeword A κ ι C :=
  ⟨interleaveWordStack u.val, by
    rw [mem_interleavedCode_iff]
    let h_u_mem := u.property
    rw [mem_codewordStack_iff] at h_u_mem
    intro k
    exact h_u_mem k
  ⟩

@[simp]
def finMapTwoWords {A : Type*} {ι : Type*} (u₀ u₁ : Word A ι)
    : WordStack A (κ := Fin 2) (ι := ι) := fun rowIdx =>
  match rowIdx with
  | ⟨0, _⟩ => u₀
  | ⟨1, _⟩ => u₁

@[simp]
def finMapTwoCodewords (u₀ u₁ : C) :
    CodewordStack A (κ := Fin 2) (ι := ι) C :=
  ⟨finMapTwoWords u₀ u₁, by
    simp only [WordStack, CodewordStack, codewordStackSet, Word, WordStack.getRowWord,
      Set.mem_setOf_eq, finMapTwoWords]
    intro k
    match k with
    | 0 => simp only [Subtype.coe_prop]
    | 1 => simp only [Subtype.coe_prop]
  ⟩

/-- Interleave two codewords u₀ and u₁ into a single interleaved codeword -/
@[simp]
def interleaveTwoWords (u₀ u₁ : Word A ι) : InterleavedWord A (Fin 2) ι :=
  interleaveWordStack (κ := Fin 2) (ι := ι) (u := finMapTwoWords u₀ u₁)

@[simp]
def interleaveTwoCodewords (u₀ u₁ : C) : InterleavedCodeword A (κ := Fin 2) ι C :=
  interleaveCodewordStack A (κ := Fin 2) (ι := ι) (u := finMapTwoCodewords A ι C u₀ u₁)

/-- Combine two codeword stacks with different κ types by stacking vertically -/
@[simp]
def finMapCodewordStacksAppend {κ₁ κ₂ : Type*}
    (u : CodewordStack A κ₁ ι C) (v : CodewordStack A κ₂ ι C) :
    CodewordStack A (Sum κ₁ κ₂) ι C :=
  ⟨fun s =>
    match s with
    | Sum.inl k₁ => u.val k₁
    | Sum.inr k₂ => v.val k₂, by
    simp only [WordStack, CodewordStack, mem_codewordStack_iff]
    intro s
    match s with
    | Sum.inl k₁ =>
      have h_u := u.property
      rw [mem_codewordStack_iff] at h_u
      simp only [WordStack.getRowWord]
      exact h_u k₁
    | Sum.inr k₂ =>
      have h_v := v.property
      rw [mem_codewordStack_iff] at h_v
      simp only [WordStack.getRowWord]
      exact h_v k₂
  ⟩

/-- Type class for overloading the interleave notation.
Interleaving a word stack -> interleaved word
Interleaving a codeword stack -> interleaved codeword -/
class Interleavable (α : Type*) (β : outParam Type*) where
  interleave : α → β
notation:65 "⋈|" u => Interleavable.interleave u

class Interleavable₂ (α : Type*) (β : outParam Type*) where
  interleave₂ : α → α → β
notation:65 u "⋈₂" v => Interleavable₂.interleave₂ u v

/-- Typeclass for interleaving codes (preserving their structure).
    For Set → Set, for ModuleCode → ModuleCode, etc. -/
class CodeInterleavable.{u, v} (Code : Type*) (InterleavedCode : outParam (Type u → Type v)) where
  interleaveCode : Code → (κ : Type u) → InterleavedCode κ

notation:20 C "^⋈" κ => @CodeInterleavable.interleaveCode _ _ _ C κ

@[simp]
instance : Interleavable (α := WordStack A κ ι) (β := InterleavedWord A κ ι) where
  interleave := interleaveWordStack

@[simp]
instance : Interleavable (α := CodewordStack A κ ι C) (β := InterleavedCodeword A κ ι C) where
  interleave u := ⟨interleaveWordStack u.val, by
    rw [mem_interleavedCode_iff]
    let h_u_mem := u.property
    rw [mem_codewordStack_iff] at h_u_mem
    intro k
    exact h_u_mem k
  ⟩

@[simp]
instance : Interleavable (α := ModuleCode.codewordStackSubmodule F A κ ι (MC := MC))
    (β := ModuleCode.moduleInterleavedCode F A κ ι (MC := MC)) where
  interleave u := interleaveCodewordStack (κ := κ) (ι := ι) (u := u)

@[simp]
instance : Interleavable₂ (α := Word A ι) (β := InterleavedWord A (Fin 2) ι) where
  interleave₂ u₀ u₁ := interleaveTwoWords A ι u₀ u₁

@[simp]
instance : Interleavable₂ (α := C) (β := InterleavedCodeword A (κ := (Fin 2)) ι C) where
  interleave₂ u₀ u₁ := interleaveTwoCodewords A ι C u₀ u₁

/-- Interleave a Set-based code into an interleaved code set. -/
@[simp]
instance : CodeInterleavable (Code := Set (ι → A))
    (InterleavedCode := fun κ => Set (Matrix ι κ A)) where
  interleaveCode C := fun κ => interleavedCodeSet (κ := κ) C

/-- Interleave a ModuleCode into an interleaved ModuleCode (preserving submodule structure). -/
@[simp]
instance : CodeInterleavable (Code := ModuleCode ι F A)
    (InterleavedCode := fun κ => ModuleCode ι F (InterleavedSymbol A κ)) where
  interleaveCode MC := fun κ => ModuleCode.moduleInterleavedCode
    (F := F) (A := A) (κ := κ) (ι := ι) (MC := MC)

omit [AddCommMonoid A] [Fintype κ] [Fintype ι] in
@[simp]
lemma interleave_wordStack_eq (u : WordStack A κ ι) : (⋈|u) = u.transpose := rfl

omit [AddCommMonoid A] [Fintype κ] [Fintype ι] in
@[simp]
lemma interleave_codewordStack_val_eq (u : CodewordStack A κ ι C) :
  (⋈| u).val = u.val.transpose := rfl

@[simp]
instance instFintypeInterleavedModuleCode [Fintype A] : Fintype (MC ^⋈ κ) := by
  exact Fintype.ofFinite ((MC ^⋈ κ) : Set (ι → (κ → A)))

@[simp]
lemma interleavedCode_eq_interleavedCodeSet {A : Type*} {ι : Type*} {κ : Type*} {C : Set (ι → A)} :
    (C ^⋈ κ) = interleavedCodeSet (κ := κ) C:= by rfl

@[simp]
lemma interleavedCode_eq_interleavedCodeSet_of_moduleCode {F A : Type*} {κ ι : Type*} [Semiring F]
    [AddCommMonoid A] [Module F A] {MC : ModuleCode ι F A} :
    ((MC ^⋈ κ) : Set (ι → (κ → A))) = interleavedCodeSet (κ := κ) (C := (MC : Set (ι → A)))
    := by rfl

@[simp]
instance {κ₁ κ₂ : Type*} :
    HAppend (WordStack A κ₁ ι) (WordStack A κ₂ ι) (WordStack A (Sum κ₁ κ₂) ι) where
  hAppend u v := fun s =>
    match s with
    | Sum.inl k₁ => u k₁
    | Sum.inr k₂ => v k₂

@[simp]
instance {κ₁ κ₂ : Type*} :
    HAppend (CodewordStack A κ₁ ι C) (CodewordStack A κ₂ ι C)
      (CodewordStack A (Sum κ₁ κ₂) ι C) where
  hAppend u v := finMapCodewordStacksAppend A ι C (κ₁ := κ₁) (κ₂ := κ₂) u v

namespace InterleavedCode

/-!
  ## Interleaved Code Structure
  Implementation of the 7-step blueprint for Interleaved Codes.
-/

variable (RowIdx SymbolIdx : Type*)
variable (RowType SymbolType CellTy : Type*)

/-! ### 1, 2, 3. Accessors -/

/-- 1. GetRow -/
class GetRow (α : Type*) (RowIdx RowType : outParam Type*) where
  getRow : (u : α) → (rowIdx : RowIdx) → RowType

/-- 2. GetSymbol -/
class GetSymbol (α : Type*) (SymbolIdx SymbolType : outParam Type*) where
  getSymbol : (u : α) → (symbolIdx : SymbolIdx) → SymbolType

/-- 3. GetCell -/
class GetCell (α : Type*) (RowIdx SymbolIdx : Type*) (CellTy : outParam Type*) where
  getCell : (u : α) → (rowIdx : RowIdx) → (symbolIdx : SymbolIdx) → CellTy

export GetRow (getRow)
export GetSymbol (getSymbol)
export GetCell (getCell)

/-- 6. InterleavedStructure: Extends accessors and defines equality via rows/symbols/cells.
    Applied to the InterleavedElementType. -/
class InterleavedStructure (α : Type*) (RowIdx SymbolIdx : outParam Type*)
    (RowType SymbolType CellTy : outParam Type*)
    extends GetRow α RowIdx RowType,
            GetSymbol α SymbolIdx SymbolType,
            GetCell α RowIdx SymbolIdx CellTy where
  eq_iff_all_rows_eq {u v : α} : u = v ↔ ∀ i, getRow u i = getRow v i
  eq_iff_all_symbols_eq {u v : α} : u = v ↔ ∀ k, getSymbol u k = getSymbol v k
  eq_iff_all_cells_eq {u v : α} : u = v ↔ ∀ i k, getCell u i k = getCell v i k

export InterleavedStructure (eq_iff_all_rows_eq eq_iff_all_symbols_eq eq_iff_all_cells_eq)

-- WordStack
@[simp] instance (priority := 500) instInterleavedStructureWordStack :
    ∀ κ, InterleavedStructure (α := WordStack A κ ι) (RowIdx := κ) (SymbolIdx := ι)
      (RowType := Word A ι) (SymbolType := InterleavedSymbol A κ) (CellTy := A) := fun κ => by
  exact {
    getRow u k := WordStack.getRowWord u k
    getSymbol u i := WordStack.getSymbol u i
    getCell u k i := (WordStack.getRowWord u k) i
    eq_iff_all_rows_eq := by
      intro u v; constructor
      · intro h; exact fun i ↦ congrFun h i
      · intro h; ext i k; exact congrFun (h i) k
    eq_iff_all_symbols_eq := by
      intro u v; constructor
      · intro h; exact fun k ↦ congrFun (congrArg Matrix.transpose h) k
      · intro h; ext i k; exact congrFun (h k) i
    eq_iff_all_cells_eq := by
      intro u v; constructor
      · intro h; exact fun i k ↦ congrFun (congrFun h i) k
      · intro h; ext i k; exact h i k
  }

-- CodewordStack
@[simp] instance instInterleavedStructureCodewordStack :
    InterleavedStructure (α := CodewordStack A κ ι C) (RowIdx := κ)
  (SymbolIdx := ι) (RowType := C) (SymbolType := InterleavedSymbol A κ) (CellTy := A) where
  getRow u k := ⟨u.val k, by -- No separate functions because CodewordStack is a subtype
    have h_u_mem := u.property
    rw [mem_codewordStack_iff] at h_u_mem
    exact h_u_mem k
  ⟩
  getSymbol u i := u.val.transpose i
  getCell u k i := u.val k i
  eq_iff_all_rows_eq := by
    intro u v; constructor
    · intro h; rw [h]; exact fun i ↦ rfl
    · intro h; ext i k;
      let res := h i; simp only [WordStack, codewordStackSet, Word, WordStack.getRowWord,
        Set.mem_setOf_eq, Subtype.mk.injEq] at res; exact congrFun res k
  eq_iff_all_symbols_eq := by
    intro u v; constructor
    · intro h; rw [h]; exact fun k ↦ rfl
    · intro h; ext i k;
      let res := h k; simp only [WordStack, codewordStackSet, Word,
        Set.mem_setOf_eq] at res; exact congrFun res i
  eq_iff_all_cells_eq := by
    intro u v; constructor
    · intro h; rw [h]; exact fun i k ↦ rfl
    · intro h; ext i k;
      let res := h i k; simp only [WordStack, codewordStackSet, Word,
        Set.mem_setOf_eq] at res; exact res

-- InterleavedWord
@[simp] instance instInterleavedStructureInterleavedWord :
    InterleavedStructure (α := InterleavedWord A κ ι) (RowIdx := κ)
  (SymbolIdx := ι) (RowType := Word A ι) (SymbolType := InterleavedSymbol A κ) (CellTy := A) where
  getRow u i := InterleavedWord.getRowWord u i
  getSymbol u k := InterleavedWord.getSymbol u k
  getCell u i k := (InterleavedWord.getRowWord u i) k
  eq_iff_all_rows_eq := by
    intro u v; constructor
    · intro h; exact fun k ↦ congrFun (congrArg Matrix.transpose h) k
    · intro h; ext i k; exact congrFun (h k) i
  eq_iff_all_symbols_eq := by
    intro u v; constructor
    · intro h; exact fun k ↦ congrFun h k
    · intro h; ext i k; exact congrFun (h i) k
  eq_iff_all_cells_eq := by
    intro u v; constructor
    · intro h; exact fun i k ↦ congrFun (congrFun h k) i
    · intro h; ext k i; exact h i k

-- InterleavedCodeword
@[simp] instance instInterleavedStructureInterleavedCodeword :
    InterleavedStructure (α := InterleavedCodeword A κ ι C) (RowIdx := κ)
  (SymbolIdx := ι) (RowType := C) (SymbolType := InterleavedSymbol A κ) (CellTy := A) where
  -- No separate functions cuz InterleavedCodeword is a subtype
  getRow u k := ⟨(Matrix.transpose u) k, by
    have h_u_mem := u.property
    rw [mem_interleavedCode_iff] at h_u_mem
    exact h_u_mem k
  ⟩
  getSymbol u colIdx := u.val colIdx
  getCell u k i := Matrix.transpose u k i
  eq_iff_all_rows_eq := by
    intro u v; constructor
    · intro h; rw [h]; exact fun i ↦ rfl
    · intro h; ext i k;
      let res := h k; simp only [Subtype.mk.injEq] at res; exact congrFun res i
  eq_iff_all_symbols_eq := by
    intro u v; constructor
    · intro h; rw [h]; exact fun k ↦ rfl
    · intro h; ext i k;
      let res := h i; simp only at res; exact congrFun res k
  eq_iff_all_cells_eq := by
    intro u v; constructor
    · intro h; rw [h]; exact fun i k ↦ rfl
    · intro h; ext i k; exact h k i

class Stackifiable (α : Type*) (β : outParam Type*) where
  stackify : α → β

notation:65 "⋈⁻¹|" u => Stackifiable.stackify u

@[simp]
instance : Stackifiable (α := InterleavedWord A κ ι) (β := WordStack A κ ι) where
  stackify u := u.transpose

@[simp]
instance : Stackifiable (α := InterleavedCodeword A κ ι C) (β := CodewordStack A κ ι C) where
  stackify u := ⟨u.val.transpose, by
    rw [mem_codewordStack_iff]
    let h_u_mem := u.property
    rw [mem_interleavedCode_iff] at h_u_mem
    intro k
    exact h_u_mem k
  ⟩

omit [AddCommMonoid A] [Fintype κ] [Fintype ι] in
/-- Used to getRow at u.val instead of getRow u -/
@[simp]
lemma getRowOfInterleavedCodeword_mem_code (C : Set (ι → A))
    (u : CodeInterleavable.interleaveCode (C) κ) (rowIdx : κ) :
    getRow (u.val) rowIdx ∈ C := by
  let getRowAsIC := getRow (show InterleavedCodeword A κ ι C from u) rowIdx
  exact getRowAsIC.property

omit [AddCommMonoid A] [Fintype κ] [Fintype ι] in
/-- Used to getRow at u.val instead of getRow u -/
@[simp]
lemma getRowOfCodewordStack_mem_code (C : Set (ι → A))
    (u : CodewordStack A κ ι C) (rowIdx : κ) :
    getRow (u.val) rowIdx ∈ C := by
  let getRowAsIC := getRow (show InterleavedCodeword A κ ι C from ⋈|u) rowIdx
  exact getRowAsIC.property

/-! ### Instances -/

variable {κ ι F A : Type*} [Fintype κ] [Fintype ι] [Semiring F] [AddCommMonoid A] [Module F A]
variable {C : Set (ι → A)}

/-! #### Instance 1: WordStack ↔ InterleavedWord (Generic Sets) -/

end InterleavedCode

/-- Notation for stacking one stack on top of another -/
infixl:65 " ++ₕ " => HAppend.hAppend

-- TODO: HasRowMembership

@[simp]
instance instNonemptyInterleavedCode [Nonempty C] :
    Nonempty (C ^⋈ κ) := by
  let c : C := Classical.arbitrary C
  use fun i k => c.val i
  intro k
  exact c.property

example (C : Set (ι → A)) : ((C ^⋈ (Fin 2))) = interleavedCodeSet (κ := Fin 2) C := by rfl
example (MC : ModuleCode ι F A) : (MC ^⋈ (Fin 2))
  = ModuleCode.moduleInterleavedCode (F := F) (A := A) (κ := Fin 2) (ι := ι) (MC := MC) := by rfl
example (u : CodewordStack A κ ι C) :
  let iuCodewords: InterleavedCodeword A κ ι C := ⋈|u
  let iuWords: InterleavedWord A κ ι := ⋈|u.val
  iuCodewords.val = iuWords
  := by rfl
example (v₀ v₁ : C) :
  let iv_codeword : InterleavedWord A (Fin 2) ι := v₀.val ⋈₂ v₁.val
  let iv_word : InterleavedCodeword A (Fin 2) ι C := v₀ ⋈₂ v₁
  iv_codeword = iv_word
  := by rfl

/-! ### Distance Properties for Interleaved Codes
**Naming conventions**:
- by default, when we say "interleaved word", it means the interleaved word of a
  `WordStack` (i.e. using notation `⋈|`).
- if the definition has `₂` at the end of its name, it means the interleaved word is of two
  `Word`s (i.e. using notation `⋈₂`).
- prefix `joint` or `pairjoint` :
  + `joint`: involves distance **from an interleaved word to the interleaved code `C^⋈ κ`**
  + `pairJoint`: involves distance **between two interleaved words**
- suffix `Nat` : the proximity is represented in terms of concrete distance (`Δ₀`),
  without this suffix, relative distance (`δᵣ`) is used instead.
-/
section JointProximityDefinitions

-- variable [DecidableEq A] [DecidableEq ι]

variable {κ ι : Type*} [Fintype ι] [Fintype κ]
  {A : Type*} (C : Set (ι → A)) [DecidableEq A]

/-- `jointProximity u δ` means the interleaved word stack `u` is within relative distance `δ` of
the interleaved code `MC^⋈ κ`. -/
def jointProximity (u : WordStack A κ ι) (δ : NNReal) : Prop :=
  let u_interleaved : InterleavedWord A κ ι := ⋈|u
  δᵣ(u_interleaved, interleavedCodeSet C) ≤ δ

/-- `jointProximity₂ u₀ u₁ e` means the interleaved pair `(u₀, u₁)` is within distance
`e` of the interleaved code `MC^⋈ (Fin 2)`. -/
def jointProximity₂ (u₀ u₁ : Word A ι) (δ : NNReal) : Prop :=
  let u_stack : WordStack A (Fin 2) ι := finMapTwoWords u₀ u₁
  jointProximity C (u := u_stack) δ

/-- `jointProximityNat u e` means the interleaved word stack `u` is within distance `e` of
the interleaved code `MC^⋈ κ`. Can use `distFromCode_le_iff_relDistFromCode_le` and
`relDistFromCode_le_iff_distFromCode_le` to prove equivalence with `jointProximity`. -/
def jointProximityNat (u : WordStack A κ ι) (e : ℕ) : Prop :=
  let u_interleaved : InterleavedWord A κ ι := ⋈|u
  Δ₀(u_interleaved, (interleavedCodeSet C)) ≤ e

/-- `jointProximityNat₂ u₀ u₁ e` means the interleaved pair `(u₀, u₁)` is within distance
`e` of the interleaved code `MC^⋈ (Fin 2)`. -/
def jointProximityNat₂ (u₀ u₁ : Word A ι) (e : ℕ) : Prop :=
  let u_stack : WordStack A (Fin 2) ι := finMapTwoWords u₀ u₁
  jointProximityNat C (u := u_stack) e

/-- `pairJointProximity u v e` means the two interleaved word stacks `u` and `v`
are within distance `e` of each other. -/
def pairJointProximity (u v : WordStack A κ ι) (e : ℕ) : Prop :=
  let u_interleaved : InterleavedWord A κ ι := ⋈|u
  let v_interleaved : InterleavedWord A κ ι := ⋈|v
  Δ₀(u_interleaved, v_interleaved) ≤ e

/-- `pairJointProximity₂ u₀ u₁ v₀ v₁ e` means the interleaved pairs `(u₀, u₁)` and `(v₀, v₁)`
  are within distance `e` of each other. -/
def pairJointProximity₂ (u₀ u₁ v₀ v₁ : Word A ι) (e : ℕ) : Prop :=
  let u_interleaved : InterleavedWord A (Fin 2) ι := u₀ ⋈₂ u₁
  let v_interleaved : InterleavedWord A (Fin 2) ι := v₀ ⋈₂ v₁
  Δ₀(u_interleaved, v_interleaved) ≤ e

theorem jointProximityNat_iff_closeToInterleavedCodeword (u : WordStack A κ ι) (e : ℕ) :
    jointProximityNat C (u := u) e ↔ ∃ (v : InterleavedCodeword A κ ι C),
      let u_interleaved : InterleavedWord A κ ι := ⋈|u
      Δ₀(u_interleaved, v.val) ≤ e := by
  unfold jointProximityNat
  let u_interleaved : InterleavedWord A κ ι := ⋈|u
  have h := Code.closeToCode_iff_closeToCodeword_of_minDist
    (C := (interleavedCodeSet C)) (u := u_interleaved) (e := e)
  constructor
  · -- Direction 1: correlatedAgreement u e → ∃ v, Δ₀(⋈|u, v) ≤ e
    intro h_corr_agree
    have res := h.mp h_corr_agree
    rcases res with ⟨v, hv_Mem, hv_dist_le_e⟩
    use ⟨v, hv_Mem⟩
  · -- Direction 2: (∃ v, Δ₀(⋈|u, v) ≤ e) → correlatedAgreement u e
    intro h_exists_v
    rcases h_exists_v with ⟨v, hvClose⟩
    have res := h.mpr (by
      use v.val
      constructor
      · exact v.property
      · exact hvClose
    )
    exact res
end JointProximityDefinitions

end Code
end InterleavedCodeDefinitions

noncomputable section

open InterleavedCode
open Code

variable {F : Type*} [Field F] [Finite F] [DecidableEq F]
         {κ : Type*} [Fintype κ]
         {ι : Type*} [Fintype ι]

local instance : Fintype F := Fintype.ofFinite F

/-- `Lemma 4.3` from `[AHIV22]`.
-/
lemma distInterleavedCodeToCodeLB
  {IC : LawfulInterleavedCode κ ι F} {U : Matrix κ ι F} {e : ℕ}
  (hF : Fintype.card F ≥ e)
  (he : (e : ℚ) ≤ (minDist (IC.1.LC : Set (ι → F)) / 3)) (hU : e < Δ(U,IC.1.MF)) :
  ∃ v ∈ Matrix.rowSpan U , e < distFromCode v IC.1.LC := sorry

namespace ProximityToRS

open ReedSolomonCode NNReal

/-- The set of points on an affine line, which are within distance `e` from a Reed-Solomon code.
-/
def closePtsOnAffineLine {ι : Type*} [Fintype ι]
                         (u v : ι → F) (deg : ℕ) (α : ι ↪ F) (e : ℕ) : Set (ι → F) :=
  {x : ι → F | x ∈ Affine.line u v ∧ distFromCode x (ReedSolomon.code α deg) ≤ e}

/-- The number of points on an affine line between, which are within distance `e` from a
Reed-Solomon code.
-/
def numberOfClosePts (u v : ι → F) (deg : ℕ) (α : ι ↪ F) (e : ℕ) : ℕ :=
  Fintype.card (closePtsOnAffineLine u v deg α e)

/-- `Lemma 4.4` from `[AHIV22]`
  Remark: Below, can use (ReedSolomonCode.minDist deg α) instead of ι - deg + 1 once proved.
-/
lemma e_leq_dist_over_3 [DecidableEq F] {deg : ℕ} {α : ι ↪ F} {e : ℕ} {u v : ι → F}
  (he : (e : ℚ) < (Code.minDist (RScodeSet α deg) : ℚ) / 3) :
  ∀ x ∈ Affine.line u v, distFromCode x (ReedSolomon.code α deg) ≤ e
  ∨ (numberOfClosePts u v deg α e) ≤ Code.minDist (RScodeSet α deg) := by sorry

/-- `Lemma 4.5` from `[AHIV22]`.
-/
lemma probOfBadPts {deg : ℕ} {α : ι ↪ F} {e : ℕ} {U : Matrix κ ι F}
  (he : (e : ℚ) < (Code.minDist (RScodeSet α deg) : ℚ) / 3)
  (hU : e < Δ(U, matrixSubmoduleOfLinearCode κ (ReedSolomon.code α deg))) :
  (PMF.uniformOfFintype (Matrix.rowSpan U)).toOuterMeasure
    { w | distFromCode (n := ι) (R := F) w (ReedSolomon.code α deg) ≤ e }
  ≤ (Code.minDist (RScodeSet α deg) : ℝ≥0) /(Fintype.card F : ℝ≥0) := by
  sorry

end ProximityToRS
end
