import DArray

/-! # Heterogeneous Records using DArray + RArray

Demonstrates using `DArray` as a flat-array replacement for Lean `structure`,
using `Lean.RArray Type` for the type-level motive to achieve O(log n) kernel
reduction per field access.

## Limitation: no field dependencies

Unlike Lean `structure`, DArray fields cannot depend on each other:
```
structure Dep where
  n : Nat
  xs : Vector Nat n  -- type depends on field `n`
```
This is impossible with DArray because the type family `α : Nat → Type` is fixed
at construction time and cannot reference other field values.
-/

open Lean (RArray)

/-! ## Small Example: Person (3 fields) -/

/-- RArray tree mapping field indices to types:
    0 → String (name), 1 → Nat (age), 2 → Bool (active).
    Built as a balanced binary search tree so each `RArray.get k` reduces
    in O(log 3) ≤ 2 kernel steps. -/
private def PersonTypes : RArray Type :=
  .branch 1 (.leaf String) (.branch 2 (.leaf Nat) (.leaf Bool))

/-- The type family for Person fields. Each `PersonMotive k` reduces in the kernel
    by traversing one path of the RArray tree (O(log n) steps). -/
abbrev PersonMotive (i : Nat) : Type := PersonTypes.get i

/-- A Person is a 3-field heterogeneous record backed by a flat Array at runtime. -/
abbrev Person := DArray PersonMotive 3

namespace Person

-- Getters (each is O(log n) to typecheck)
abbrev name (p : Person) : String := p.get ⟨0, by omega⟩
abbrev age (p : Person) : Nat := p.get ⟨1, by omega⟩
abbrev active (p : Person) : Bool := p.get ⟨2, by omega⟩

-- Setters
abbrev setName (p : Person) (v : String) : Person := p.set ⟨0, by omega⟩ v
abbrev setAge (p : Person) (v : Nat) : Person := p.set ⟨1, by omega⟩ v
abbrev setActive (p : Person) (v : Bool) : Person := p.set ⟨2, by omega⟩ v

-- Modifiers
abbrev modifyName (p : Person) (f : String → String) : Person := p.modify ⟨0, by omega⟩ f
abbrev modifyAge (p : Person) (f : Nat → Nat) : Person := p.modify ⟨1, by omega⟩ f
abbrev modifyActive (p : Person) (f : Bool → Bool) : Person := p.modify ⟨2, by omega⟩ f

/-- Constructor via push chain. Each push is O(log n) to typecheck because the
    kernel only needs to reduce `PersonMotive k` for the concrete index `k`. -/
def mk (name : String) (age : Nat) (active : Bool) : Person :=
  (DArray.mkEmpty 3).push name |>.push age |>.push active

end Person

/-! ## Scaled-up Example: 1000 fields (all Nat)

Demonstrates that the RArray motive scales: each accessor typechecks in
O(log n) kernel reduction steps, regardless of how many fields exist.

For *heterogeneous* fields (different types per field), the balanced tree would
be built at elaboration time using `Lean.RArray.ofFn` and embedded as a concrete
`.branch`/`.leaf` literal via `RArray.toExpr` — that requires metaprogramming
(a future extension).

For *homogeneous* fields (all the same type), we build a complete binary tree
using structural recursion, which the kernel can reduce (unlike well-founded
recursion). The tree has all pivots at 0, so `Nat.ble 0 i = true` for any `i`
and the kernel always goes right — but since all leaves are identical, the
result is correct. -/

/-- Build a complete binary tree of depth `d` where every leaf holds `v`.
    Uses structural recursion on `Nat`, which the kernel *can* reduce
    (unlike well-founded recursion). -/
private def mkConstTree (v : α) : Nat → RArray α
  | 0 => .leaf v
  | d + 1 => .branch 0 (mkConstTree v d) (mkConstTree v d)

/-- Balanced tree of depth 10 (covers 2^10 = 1024 ≥ 1000 indices).
    `BigTypes.get k` reduces to `Nat` in ≤ 10 kernel steps for any `k`. -/
private def BigTypes : RArray Type := mkConstTree Nat 10

/-- Type family for a 1000-field record where every field is `Nat`. -/
abbrev BigMotive (i : Nat) : Type := BigTypes.get i

/-- A 1000-field record. At runtime, just a flat Array of 1000 slots. -/
abbrev BigRecord := DArray BigMotive 1000

namespace BigRecord

-- Sample accessors — each typechecks in O(log 1000) ≈ 10 kernel steps
abbrev get0 (r : BigRecord) : Nat := r.get ⟨0, by omega⟩
abbrev get500 (r : BigRecord) : Nat := r.get ⟨500, by omega⟩
abbrev get999 (r : BigRecord) : Nat := r.get ⟨999, by omega⟩

abbrev set500 (r : BigRecord) (v : Nat) : BigRecord := r.set ⟨500, by omega⟩ v

/-- Constructor. Since all pivots are 0 and `Nat.ble 0 i = true` for any `i`,
    the kernel reduces `BigMotive i` to `Nat` even for variable `i`, so
    `DArray.ofFn` typechecks directly. -/
def mk (f : Fin 1000 → Nat) : BigRecord :=
  DArray.ofFn (fun i => f i)

end BigRecord

/-! ## Runtime tests -/

def main : IO Unit := do
  IO.println "=== Person ==="
  let p := Person.mk "Alice" 30 true
  IO.println s!"  name: {p.name}"
  IO.println s!"  age: {p.age}"
  IO.println s!"  active: {p.active}"

  let p2 := p.setName "Bob" |>.modifyAge (· + 1) |>.setActive false
  IO.println s!"  updated: name={p2.name} age={p2.age} active={p2.active}"

  assert! p.name == "Alice"
  assert! p.age == 30
  assert! p.active == true
  assert! p2.name == "Bob"
  assert! p2.age == 31
  assert! p2.active == false
  IO.println "  Person tests passed"

  IO.println "=== BigRecord (1000 fields) ==="
  let big := BigRecord.mk (fun i => i.val)
  IO.println s!"  get0: {big.get0}"
  IO.println s!"  get500: {big.get500}"
  IO.println s!"  get999: {big.get999}"

  assert! big.get0 == 0
  assert! big.get500 == 500
  assert! big.get999 == 999

  let big2 := big.set500 42
  assert! big2.get500 == 42
  assert! big2.get0 == 0
  IO.println "  BigRecord tests passed"

  IO.println "all tests passed!"
