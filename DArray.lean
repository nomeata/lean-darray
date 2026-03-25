/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

universe u v w

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
@[noinline] def mkEmpty (_ : Nat) : DArray α 0 := ⟨fun i => Fin.elim0 i⟩

/-- The empty DArray. -/
def empty : DArray α 0 := mkEmpty 0

/-- Get the element at index `i`. -/
@[noinline] def get (a : DArray α n) (i : Fin n) : α i := a.fn i

/-- Push a new element onto the end. -/
@[noinline] def push (a : DArray α n) (v : α n) : DArray α (n + 1) := ⟨fun ⟨i, h⟩ =>
  if h₂ : i < n then
    a.fn ⟨i, h₂⟩
  else
    have : i = n := Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.ge_of_not_lt h₂)
    this ▸ v⟩

/-- Set the element at index `i`. -/
@[noinline] def set (a : DArray α n) (i : Fin n) (v : α i) : DArray α n := ⟨fun j =>
  if h : j = i then h ▸ v
  else a.fn j⟩

/-- Get the size. -/
@[noinline] def size (_ : DArray α n) : Nat := n

/-- Create a DArray from a function. -/
@[noinline] def ofFn (f : (i : Fin n) → α i) : DArray α n := ⟨f⟩

/-- Remove the last element. -/
@[noinline] def pop (a : DArray α (n + 1)) : DArray α n :=
  ⟨fun ⟨i, hi⟩ => a.fn ⟨i, by omega⟩⟩

/-- Modify the element at index `i` by applying `f`. -/
@[noinline] def modify (a : DArray α n) (i : Fin n) (f : α i → α i) : DArray α n :=
  a.set i (f (a.get i))

/-- Map a dependent function over all elements. -/
@[noinline] def map {β : Nat → Type u} (a : DArray α n) (f : (i : Fin n) → α i → β i) : DArray β n :=
  ⟨fun i => f i (a.fn i)⟩

/-- Take the first `k` elements. -/
@[noinline] def take (a : DArray α n) (k : Nat) (h : k ≤ n) : DArray α k :=
  ⟨fun ⟨i, hi⟩ => a.fn ⟨i, by omega⟩⟩

/-- Append two DArrays. The second array's type family must be shifted by `n`. -/
@[noinline] def append {m : Nat} (a : DArray α n) (b : DArray (fun i => α (n + i)) m) :
    DArray α (n + m) :=
  ⟨fun ⟨i, h⟩ =>
    if h₂ : i < n then
      a.fn ⟨i, h₂⟩
    else
      have h₃ : i - n < m := by omega
      cast (congrArg α (show n + (i - n) = i by omega)) (b.fn ⟨i - n, h₃⟩)⟩

/-- Combine two DArrays element-wise using a function. -/
@[noinline] def zipWith {β γ : Nat → Type u} (a : DArray α n) (b : DArray β n)
    (f : (i : Fin n) → α i → β i → γ i) : DArray γ n :=
  ⟨fun i => f i (a.fn i) (b.fn i)⟩

/-- Reverse the array. Element at index `i` moves to index `n - 1 - i`. -/
@[noinline] def reverse (a : DArray α n) : DArray (fun i => α (n - 1 - i)) n :=
  ⟨fun ⟨i, hi⟩ => a.fn ⟨n - 1 - i, by omega⟩⟩

/-- Create a DArray of `n` copies of the same value. -/
@[noinline] def replicate {β : Type u} (n : Nat) (v : β) : DArray (fun _ => β) n :=
  ⟨fun _ => v⟩

/-- Cast a DArray to a different size, given a proof of equality. -/
@[noinline] def cast {m : Nat} (h : n = m) (a : DArray α n) : DArray α m := h ▸ a

/-- Map a monadic function over all elements, left to right. -/
@[noinline] def mapM {m : Type u → Type v} [Monad m] {β : Nat → Type u}
    (a : DArray α n) (f : (i : Fin n) → α i → m (β i)) : m (DArray β n) :=
  go 0 (Nat.zero_le n) .empty
where
  go (k : Nat) (hk : k ≤ n) (acc : DArray β k) : m (DArray β n) := do
    if hlt : k < n then
      let v ← f ⟨k, hlt⟩ (a.get ⟨k, hlt⟩)
      go (k + 1) hlt (acc.push v)
    else
      have : k = n := by omega
      return this ▸ acc
  termination_by n - k

/-! ## Unsafe Array-backed implementations

At runtime, a `DArray` value is represented as an `Array`. All operations
are redirected to the corresponding `Array` operations via `@[implemented_by]`.
This is sound because all boxed Lean types have the same runtime
representation (`lean_object*`). -/

private unsafe def mkEmptyImpl (_ : Nat) : DArray α 0 :=
  unsafeCast (Array.mkEmpty 0 : Array PUnit.{1})

private unsafe def getImpl (a : DArray α n) (i : Fin n) : α i :=
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

private unsafe def ofFnImpl (f : (i : Fin n) → α i) : DArray α n :=
  unsafeCast (Array.ofFn (n := n) (fun i => (unsafeCast (f i) : PUnit.{1})))

private unsafe def popImpl (a : DArray α (n + 1)) : DArray α n :=
  let arr : Array PUnit.{1} := unsafeCast a
  unsafeCast arr.pop

private unsafe def modifyImpl (a : DArray α n) (i : Fin n) (f : α i → α i) : DArray α n :=
  let arr : Array PUnit.{1} := unsafeCast a
  let v : α i := unsafeCast (arr[i.val]'lcProof)
  let arr := arr.set i.val (unsafeCast (f v)) lcProof
  unsafeCast arr

private unsafe def mapImpl {β : Nat → Type u} (a : DArray α n)
    (f : (i : Fin n) → α i → β i) : DArray β n :=
  let arr : Array PUnit.{1} := unsafeCast a
  let result : Array PUnit.{1} := Id.run do
    let mut result : Array PUnit.{1} := Array.mkEmpty n
    for h : i in [:n] do
      result := Array.push result (unsafeCast (f ⟨i, h.upper⟩ (unsafeCast (arr[i]'lcProof))))
    return result
  unsafeCast result

private unsafe def takeImpl (a : DArray α n) (k : Nat) (_ : k ≤ n) : DArray α k :=
  let arr : Array PUnit.{1} := unsafeCast a
  unsafeCast (arr.extract 0 k)

private unsafe def appendImpl {m : Nat} (a : DArray α n)
    (b : DArray (fun i => α (n + i)) m) : DArray α (n + m) :=
  let arr1 : Array PUnit.{1} := unsafeCast a
  let arr2 : Array PUnit.{1} := unsafeCast b
  unsafeCast (arr1 ++ arr2)

private unsafe def zipWithImpl {β γ : Nat → Type u} (a : DArray α n) (b : DArray β n)
    (f : (i : Fin n) → α i → β i → γ i) : DArray γ n :=
  let arr1 : Array PUnit.{1} := unsafeCast a
  let arr2 : Array PUnit.{1} := unsafeCast b
  let result : Array PUnit.{1} := Id.run do
    let mut result : Array PUnit.{1} := Array.mkEmpty n
    for h : i in [:n] do
      result := Array.push result
        (unsafeCast (f ⟨i, h.upper⟩ (unsafeCast (arr1[i]'lcProof))
          (unsafeCast (arr2[i]'lcProof))))
    return result
  unsafeCast result

private unsafe def reverseImpl (a : DArray α n) : DArray (fun i => α (n - 1 - i)) n :=
  let arr : Array PUnit.{1} := unsafeCast a
  unsafeCast arr.reverse

private unsafe def replicateImpl {β : Type u} (n : Nat) (v : β) : DArray (fun _ => β) n :=
  let arr : Array PUnit.{1} := Id.run do
    let mut arr : Array PUnit.{1} := Array.mkEmpty n
    for _ in [:n] do
      arr := Array.push arr (unsafeCast v)
    return arr
  unsafeCast arr

private unsafe def castImpl {m : Nat} (_ : n = m) (a : DArray α n) : DArray α m :=
  unsafeCast a

private unsafe def mapMImpl {m : Type u → Type v} [Monad m] {β : Nat → Type u}
    (a : DArray α n) (f : (i : Fin n) → α i → m (β i)) : m (DArray β n) := do
  let arr : Array PUnit.{u+1} := unsafeCast a
  let mut result : Array PUnit.{u+1} := Array.mkEmpty n
  for h : i in [:n] do
    let v ← f ⟨i, h.upper⟩ (unsafeCast (arr[i]'lcProof))
    let w : PUnit.{u+1} := unsafeCast v
    result := Array.push result w
  return unsafeCast result

attribute [implemented_by mkEmptyImpl] mkEmpty
attribute [implemented_by getImpl] get
attribute [implemented_by pushImpl] push
attribute [implemented_by setImpl] set
attribute [implemented_by sizeImpl] size
attribute [implemented_by ofFnImpl] ofFn
attribute [implemented_by popImpl] pop
attribute [implemented_by modifyImpl] modify
attribute [implemented_by mapImpl] map
attribute [implemented_by takeImpl] take
attribute [implemented_by appendImpl] append
attribute [implemented_by zipWithImpl] zipWith
attribute [implemented_by reverseImpl] reverse
attribute [implemented_by replicateImpl] replicate
attribute [implemented_by castImpl] cast
attribute [implemented_by mapMImpl] mapM

/-! ## Derived operations -/

/-- Get element at index `i`, or default if out of bounds. -/
@[inline] def getD (a : DArray α n) (i : Nat) (v₀ : α i) : α i :=
  if h : i < n then a.get ⟨i, h⟩ else v₀

/-- Create a singleton DArray. -/
@[inline] def singleton (v : α 0) : DArray α 1 := empty.push v

/-- Check if the array is empty. -/
@[inline] def isEmpty (_ : DArray α n) : Bool := n == 0

/-- Get the first element. -/
@[inline] def head (a : DArray α (n + 1)) : α 0 := a.get ⟨0, by omega⟩

/-- Get the last element. -/
@[inline] def back (a : DArray α (n + 1)) : α n := a.get ⟨n, by omega⟩

/-- Set the element at index `i` if `i` is in bounds, otherwise return unchanged. -/
@[inline] def setIfInBounds (a : DArray α n) (i : Nat) (v : α i) : DArray α n :=
  if h : i < n then a.set ⟨i, h⟩ v else a

/-- Left fold over all elements with index. -/
@[inline] def foldl {β : Type v} (a : DArray α n)
    (f : (i : Fin n) → β → α i → β) (init : β) : β := Id.run do
  let mut r := init
  for h : i in [:n] do
    r := f ⟨i, h.upper⟩ r (a.get ⟨i, h.upper⟩)
  return r

/-- Right fold over all elements with index. -/
def foldr {β : Type v} (a : DArray α n)
    (f : (i : Fin n) → α i → β → β) (init : β) : β :=
  go n (Nat.le_refl n) init
where
  go (k : Nat) (hk : k ≤ n) (acc : β) : β :=
    match k with
    | 0 => acc
    | k + 1 =>
      let fi : Fin n := ⟨k, by omega⟩
      go k (by omega) (f fi (a.get fi) acc)

/-- Check if any element satisfies the predicate. -/
@[inline] def any (a : DArray α n) (p : (i : Fin n) → α i → Bool) : Bool := Id.run do
  for h : i in [:n] do
    if p ⟨i, h.upper⟩ (a.get ⟨i, h.upper⟩) then return true
  return false

/-- Check if all elements satisfy the predicate. -/
@[inline] def all (a : DArray α n) (p : (i : Fin n) → α i → Bool) : Bool := Id.run do
  for h : i in [:n] do
    if !p ⟨i, h.upper⟩ (a.get ⟨i, h.upper⟩) then return false
  return true

/-- Find the first index satisfying the predicate. -/
def findIdx? (a : DArray α n) (p : (i : Fin n) → α i → Bool) : Option (Fin n) := Id.run do
  for h : i in [:n] do
    let fi : Fin n := ⟨i, h.upper⟩
    if p fi (a.get fi) then return some fi
  return none

/-- Apply `f` to each element and return the first `some` result. -/
def findSome? {β : Type v} (a : DArray α n)
    (f : (i : Fin n) → α i → Option β) : Option β := Id.run do
  for h : i in [:n] do
    let fi : Fin n := ⟨i, h.upper⟩
    if let some v := f fi (a.get fi) then return some v
  return none

/-- Map all elements to a plain `Array`. -/
def toArray {β : Type v} (a : DArray α n) (f : ∀ i, α i → β) : Array β := Id.run do
  let mut r : Array β := Array.mkEmpty n
  for h : i in [:n] do
    r := r.push (f i (a.get ⟨i, h.upper⟩))
  return r

/-- Convert to a `List` by mapping each element. -/
def toList {β : Type v} (a : DArray α n) (f : ∀ i, α i → β) : List β :=
  (a.toArray f).toList

/-- Combine two DArrays element-wise into pairs. -/
def zip {β : Nat → Type u} (a : DArray α n) (b : DArray β n) :
    DArray (fun i => α i × β i) n :=
  a.zipWith b (fun _ x y => (x, y))

/-- Drop the first `k` elements. -/
def drop (a : DArray α n) (k : Nat) (h : k ≤ n) :
    DArray (fun i => α (k + i)) (n - k) :=
  ofFn fun ⟨i, hi⟩ => a.get ⟨k + i, by omega⟩

/-- Extract a subrange `[start, stop)`. -/
def extract (a : DArray α n) (start stop : Nat) (h₁ : start ≤ stop) (h₂ : stop ≤ n) :
    DArray (fun i => α (start + i)) (stop - start) :=
  ofFn fun ⟨i, hi⟩ => a.get ⟨start + i, by omega⟩

/-- Shrink the array to size `k`. Alias for `take`. -/
abbrev shrink := @take

/-! ## Monadic operations -/

/-- Left fold with a monadic accumulator. -/
@[inline] def foldlM {m : Type v → Type w} [Monad m] {β : Type v}
    (a : DArray α n) (f : (i : Fin n) → β → α i → m β) (init : β) : m β := do
  let mut r := init
  for h : i in [:n] do
    r ← f ⟨i, h.upper⟩ r (a.get ⟨i, h.upper⟩)
  return r

/-- Right fold with a monadic accumulator. -/
def foldrM {m : Type v → Type w} [Monad m] {β : Type v}
    (a : DArray α n) (f : (i : Fin n) → α i → β → m β) (init : β) : m β :=
  go n (Nat.le_refl n) init
where
  go (k : Nat) (hk : k ≤ n) (acc : β) : m β := do
    match k with
    | 0 => return acc
    | k + 1 =>
      let fi : Fin n := ⟨k, by omega⟩
      let acc' ← f fi (a.get fi) acc
      go k (by omega) acc'

/-- Apply a monadic action to each element. -/
@[inline] def forM {m : Type v → Type w} [Monad m]
    (a : DArray α n) (f : (i : Fin n) → α i → m PUnit) : m PUnit := do
  for h : i in [:n] do
    f ⟨i, h.upper⟩ (a.get ⟨i, h.upper⟩)

/-- Iterate over elements with early termination support. -/
def forIn {m : Type v → Type w} [Monad m] {β : Type v}
    (a : DArray α n) (init : β) (f : (i : Fin n) → α i → β → m (ForInStep β)) : m β :=
  go 0 init
where
  go (k : Nat) (acc : β) : m β := do
    if hlt : k < n then
      match ← f ⟨k, hlt⟩ (a.get ⟨k, hlt⟩) acc with
      | .done b => return b
      | .yield b => go (k + 1) b
    else return acc
  termination_by n - k

/-- Check if any element satisfies a monadic predicate. -/
@[inline] def anyM {m : Type → Type w} [Monad m]
    (a : DArray α n) (p : (i : Fin n) → α i → m Bool) : m Bool := do
  for h : i in [:n] do
    if ← p ⟨i, h.upper⟩ (a.get ⟨i, h.upper⟩) then return true
  return false

/-- Check if all elements satisfy a monadic predicate. -/
@[inline] def allM {m : Type → Type w} [Monad m]
    (a : DArray α n) (p : (i : Fin n) → α i → m Bool) : m Bool := do
  for h : i in [:n] do
    if !(← p ⟨i, h.upper⟩ (a.get ⟨i, h.upper⟩)) then return false
  return true

/-! ## Theorems and instances -/

/-- Two DArrays are equal iff they agree at every index. -/
@[ext] theorem ext {a b : DArray α n} (h : ∀ i, a.get i = b.get i) : a = b := by
  cases a; cases b; congr 1; funext i; exact h i

/-- Decidable equality for DArrays, given decidable equality at each index. -/
private def decEq [inst : ∀ i, DecidableEq (α i)] (a b : DArray α n) : Decidable (a = b) :=
  go 0 (Nat.zero_le n) (fun _ h => absurd h (Nat.not_lt_zero _))
where
  go (k : Nat) (hk : k ≤ n) (heq : ∀ i : Fin n, i.val < k → a.get i = b.get i) :
      Decidable (a = b) :=
    if hlt : k < n then
      if h : a.get ⟨k, hlt⟩ = b.get ⟨k, hlt⟩ then
        go (k + 1) hlt fun fi hfi =>
          if hfik : fi.val < k then heq fi hfik
          else by
            have hle : fi.val ≤ k := Nat.lt_succ_iff.mp hfi
            have hge : fi.val ≥ k := Nat.ge_of_not_lt hfik
            have hval : fi.val = k := Nat.le_antisymm hle hge
            have hfin : fi = ⟨k, hlt⟩ := Fin.ext hval
            rw [hfin]; exact h
      else .isFalse fun hab => h (hab ▸ rfl)
    else .isTrue (ext fun i => heq i (by omega))
  termination_by n - k

instance [∀ i, DecidableEq (α i)] : DecidableEq (DArray α n) := decEq

instance [∀ i, Inhabited (α i)] : Inhabited (DArray α n) where
  default := ofFn fun _ => default

instance [∀ i, BEq (α i)] : BEq (DArray α n) where
  beq a b := Id.run do
    for h : i in [:n] do
      if a.get ⟨i, h.upper⟩ != b.get ⟨i, h.upper⟩ then return false
    return true

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
