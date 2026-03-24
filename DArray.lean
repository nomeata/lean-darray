/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

universe u

/--
A dependent array where the element at index `i` has type `α i`.
Backed by a native `Array` at runtime via `@[implemented_by]`.
-/
structure DArray (α : Nat → Type u) (n : Nat) where
  private mk ::
  private fn : (i : Fin n) → α i

namespace DArray

variable {α : Nat → Type u} {n : Nat}

/-! ## Core operations (logical model) -/

/-- Create an empty DArray with a capacity hint. -/
def mkEmpty (_ : Nat) : DArray α 0 := ⟨fun i => Fin.elim0 i⟩

/-- The empty DArray. -/
def empty : DArray α 0 := mkEmpty 0

/-- Get the element at index `i`. -/
def get (a : DArray α n) (i : Fin n) : α i := a.fn i

/-- Push a new element onto the end. -/
def push (a : DArray α n) (v : α n) : DArray α (n + 1) := ⟨fun ⟨i, h⟩ =>
  if h₂ : i < n then
    a.fn ⟨i, h₂⟩
  else
    have : i = n := Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.ge_of_not_lt h₂)
    this ▸ v⟩

/-- Set the element at index `i`. -/
def set (a : DArray α n) (i : Fin n) (v : α i) : DArray α n := ⟨fun j =>
  if h : j = i then h ▸ v
  else a.fn j⟩

/-- Get the size. -/
def size (_ : DArray α n) : Nat := n

/-! ## Unsafe Array-backed implementations

At runtime, a `DArray` value is represented as an `Array`. All operations
are redirected to the corresponding `Array` operations via `@[implemented_by]`.
This is sound because all boxed Lean types have the same runtime
representation (`lean_object*`). -/

private unsafe def mkEmptyImpl (_ : Nat) : DArray α 0 :=
  unsafeCast (Array.mkEmpty 0 : Array PUnit.{1})

@[noinline] private unsafe def getImpl (a : DArray α n) (i : Fin n) : α i :=
  let arr : Array PUnit.{1} := unsafeCast a
  unsafeCast (arr[i.val]'lcProof)

private unsafe def pushImpl (a : DArray α n) (v : α n) : DArray α (n + 1) :=
  let arr : Array PUnit.{1} := unsafeCast a
  unsafeCast (arr.push (unsafeCast v))

private unsafe def setImpl (a : DArray α n) (i : Fin n) (v : α i) : DArray α n :=
  let arr : Array PUnit.{1} := unsafeCast a
  let arr := arr.set i.val (unsafeCast v) lcProof
  unsafeCast arr

private unsafe def sizeImpl (a : DArray α n) : Nat :=
  (unsafeCast a : Array PUnit.{1}).size

attribute [implemented_by mkEmptyImpl] mkEmpty
attribute [implemented_by getImpl] get
attribute [implemented_by pushImpl] push
attribute [implemented_by setImpl] set
attribute [implemented_by sizeImpl] size

/-! ## Derived operations -/

/-- Get element at index `i`, or default if out of bounds. -/
@[inline] def getD (a : DArray α n) (i : Nat) (v₀ : α i) : α i :=
  if h : i < n then a.get ⟨i, h⟩ else v₀

/-- Map all elements to a plain `Array`. -/
def toArray {β : Type _} (a : DArray α n) (f : ∀ i, α i → β) : Array β := Id.run do
  let mut r : Array β := Array.mkEmpty n
  for h : i in [:n] do
    r := r.push (f i (a.get ⟨i, h.upper⟩))
  return r

instance [∀ i, Repr (α i)] : Repr (DArray α n) where
  reprPrec a _ :=
    let items := a.toArray (fun _ x => repr x)
    if n == 0 then
      "#[]"
    else
      Std.Format.bracketFill "#[" (Std.Format.joinSep items.toList ("," ++ Std.Format.line)) "]"

instance [∀ i, ToString (α i)] : ToString (DArray α n) where
  toString a := toString (a.toArray (fun _ => toString))

end DArray
