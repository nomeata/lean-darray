universe u

set_option autoImplicit false

variable (α : Nat → Type u)

structure DArray : Type u where mk ::
  size : Nat
  vals : (i : Fin size) → α i

-- TODO: Override mk
-- attribute [extern "lean_array_size"] DArray.mk

-- attribute [extern "lean_array_get_size"] DArray.size

namespace DArray

variable {α : Nat → Type u}

@[extern "lean_array_get_size"]
def size' (a : @& DArray α) : Nat := a.size

-- @[nolint unusedVariables]
@[extern "lean_mk_empty_array_with_capacity"]
def mkEmpty (_ : @& Nat): DArray α := ⟨0, fun i => Fin.elim0 i⟩

instance : Repr (DArray α) where
  reprPrec a _ := repr a.size

def empty : DArray α := mkEmpty 0

def ex0 : DArray (fun _ => Nat) := DArray.empty

@[extern "lean_array_fget"]
def get (a : @& DArray α) (i : @& Fin a.size) : α i := a.vals i

@[inline] abbrev getD (a : DArray α) (i : Nat) (v₀ : α i) : α i :=
  dite (LT.lt i a.size) (fun h => a.get ⟨i, h⟩) (fun _ => v₀)

@[extern "lean_array_push"]
def push (a : DArray α) (v : α a.size) : DArray α where
  size := a.size + 1
  vals := fun ⟨i, h⟩ =>
    if h2 : i < a.size then
      a.get ⟨i, h2⟩
    else
      have heq : i = a.size :=
        Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.ge_of_not_lt h2)
      heq ▸ v


@[extern "lean_array_fset"]
def set (a : DArray α) (i : @& Fin a.size) (v : α i) : DArray α where
  size := a.size
  vals := fun j =>
    if h : j = i then
      h ▸ v 
    else
      a.get j
  
def mapToArray {β} (a : DArray α) (f : ∀ i, α i → β) : Array β := Id.run $ do
  let mut a' := .empty
  let mut i := 0
  while h : i < a.size' do
    a' := a'.push (f i (a.get ⟨i, h⟩))
    i := i+1
  pure a'


instance [∀ i, Repr (α i)] : Repr (DArray α) where
  reprPrec a _ :=
    let a' : Array Std.Format := a.mapToArray (fun _ => repr)
    if a.size == 0 then
      "#[]"
    else
      Std.Format.bracketFill "#[" (Std.Format.joinSep (a'.toList) ("," ++ Std.Format.line)) "]"

instance [∀ i, ToString (α i)] : ToString (DArray α) where
  toString a :=
    let a' : Array String := a.mapToArray (fun _ => toString)
    toString a'

end DArray


def ex1 : DArray (fun _ => Nat) :=
  DArray.empty |>.push 1 |>.push 2

def ex2 : Nat := ex1.get ⟨1, Nat.lt_of_succ_le (Nat.le_refl 2)⟩ 

variable (α : Type _)
variable (β : Type _)


def Nat.even : Nat → Bool 
 | 0 => true
 | n + 1 => not n.even

theorem Nat.even_two_times (i : Nat) : (2 * i).even := by
  induction i
  case zero => rfl
  case succ i ih => exact Eq.trans (Bool.not_not _) ih

theorem Nat.two_times_succ_lt_of_lt_of_even (i n : Nat) (h2 : i < n/2) :
    2 * i + 1 < n := Nat.lt_of_succ_le $ calc
  2 * i + 2 = 2 * (i + 1) := rfl
  _ ≤ 2 * (n/2) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h2) 
  _ ≤ 2 * (n/2) + n % 2 := Nat.le_add_right _ _
  _ = n := Nat.div_add_mod n 2

theorem Nat.two_times_lt_of_lt_of_even (i n : Nat) (h2 : i < n/2) :
    2 * i < n := calc
  2 * i < 2 * i + 1 := Nat.lt_succ_self _
  _ < n := Nat.two_times_succ_lt_of_lt_of_even  i n h2

def Alternating := (fun i : Nat => if i.even then α else β)

structure ArrayPair where
  arr : DArray (Alternating α β)
  heven : arr.size.even

namespace  ArrayPair

variable {α : Type _}
variable {β : Type _}

def Alternating.even {i : Nat} (h : i.even) : Alternating α β i = α := by
  unfold Alternating
  simp [h]

def Alternating.even_succ {i : Nat} (h : i.even) : Alternating α β (i+1) = β := by
  unfold Alternating
  simp [h, Nat.even]

def Alternating.odd {i : Nat} (h : ¬i.even) : Alternating α β i = β := by
  cases i
  case zero => simp at h
  case succ i =>
    have h' : i.even = true := by
      unfold Nat.even at h
      simp at h
      exact h
    exact Alternating.even_succ h'

def Alternating.two_times (i : Nat) : Alternating α β (2 * i) = α := by
  apply Alternating.even
  apply Nat.even_two_times 

def Alternating.two_times_succ (i : Nat) : Alternating α β (2 * i + 1) = β := by
  apply Alternating.even_succ
  apply Nat.even_two_times 

def empty : ArrayPair α β := .mk .empty rfl

def push (a : ArrayPair α β) (p : α × β) : ArrayPair α β :=
  let (x, y) := p
  { arr := a.arr
      |>.push (Alternating.even a.heven ▸ x)
      |>.push (Alternating.even_succ a.heven ▸ y),
    heven := by
      show ((a.arr.size + 1 + 1).even)
      dsimp [Nat.even]
      rw [Bool.not_not]
      exact a.heven
  }

def size (a : ArrayPair α β) : Nat := a.arr.size / 2

def getFst (a : ArrayPair α β) : Fin a.size → α := fun ⟨i, hi⟩ =>
  let j : Fin a.arr.size := ⟨2 * i, Nat.two_times_lt_of_lt_of_even i a.arr.size hi ⟩
  @Alternating.two_times α β i ▸ a.arr.get j

def getSnd (a : ArrayPair α β) : Fin a.size → β := fun ⟨i, hi⟩ =>
  let j : Fin a.arr.size := ⟨2 * i + 1, Nat.two_times_succ_lt_of_lt_of_even i a.arr.size hi ⟩
  @Alternating.two_times_succ α β i ▸ a.arr.get j

def get (a : ArrayPair α β) (i : Fin a.size) : (α × β) := (a.getFst i, a.getSnd i)

def setFst (a : ArrayPair α β) : Fin a.size → α → ArrayPair α β := fun ⟨i, hi⟩ x =>
  let j : Fin a.arr.size := ⟨2 * i, Nat.two_times_lt_of_lt_of_even i a.arr.size hi ⟩
  let x : Alternating α β (2 * i) := (@Alternating.two_times α β i).symm ▸ x
  { a with arr := a.arr.set j x }

def setSnd (a : ArrayPair α β) : Fin a.size → β → ArrayPair α β := fun ⟨i, hi⟩ y =>
  let j : Fin a.arr.size := ⟨2 * i + 1, Nat.two_times_succ_lt_of_lt_of_even i a.arr.size hi ⟩
  let y : Alternating α β (2 * i + 1) := (@Alternating.two_times_succ α β i).symm ▸ y
  { a with arr := a.arr.set j y }

def set (a : ArrayPair α β) (i : Fin a.size) : α × β → ArrayPair α β := fun (x,y) =>
  a |>.setFst i x |>.setSnd i y

instance [ToString α] [ToString β] (i : Nat) : ToString (Alternating α β i) where
  toString x := if h : i.even then
    toString (@Alternating.even α β i h ▸ x : α)
  else
    toString (@Alternating.odd α β i h ▸ x : β)

instance [ToString α] [ToString β] : ToString (ArrayPair α β) where
  toString a := toString a.arr

end ArrayPair
