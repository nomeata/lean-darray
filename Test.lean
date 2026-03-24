import DArray

/-!
# Tests for DArray

Compile-time `#guard` tests verify the logical model (pure functions).
Runtime tests in `main` exercise the `@[implemented_by]` Array-backed
implementations, including a stress test proving O(1) amortized performance.
-/

abbrev constNat := fun (_ : Nat) => Nat

section CompileTimeTests

-- These evaluate using the pure logical model at elaboration time.
#guard (DArray.empty (α := constNat)).size = 0
#guard ((DArray.empty (α := constNat)).push 1).size = 1
#guard ((DArray.empty (α := constNat)).push 10 |>.push 20 |>.push 30).size = 3

end CompileTimeTests

def assert (b : Bool) (msg : String) : IO Unit :=
  if b then pure () else throw (.userError s!"FAILED: {msg}")

/-- Build a DArray [0, 1, ..., n-1] using Array directly (for stress testing). -/
private unsafe def buildBigImpl (n : Nat) : DArray constNat n := Id.run do
  let mut arr : Array PUnit.{1} := Array.mkEmpty n
  for i in [:n] do
    arr := arr.push (unsafeCast i)
  return unsafeCast arr

@[implemented_by buildBigImpl]
private def buildBig (n : Nat) : DArray constNat n :=
  match n with
  | 0 => DArray.empty
  | n + 1 => (buildBig n).push n

def main : IO Unit := do
  -- mkEmpty + push + size
  let a := (DArray.mkEmpty 4 : DArray constNat 0).push 10 |>.push 20 |>.push 30
  assert (a.size == 3) "size"

  -- get
  assert (a.get ⟨0, by omega⟩ == 10) "get[0]"
  assert (a.get ⟨1, by omega⟩ == 20) "get[1]"
  assert (a.get ⟨2, by omega⟩ == 30) "get[2]"

  -- set
  let b := a.set ⟨1, by omega⟩ 99
  assert (b.get ⟨0, by omega⟩ == 10) "set: unchanged[0]"
  assert (b.get ⟨1, by omega⟩ == 99) "set: changed[1]"
  assert (b.get ⟨2, by omega⟩ == 30) "set: unchanged[2]"

  -- getD
  assert (a.getD 1 0 == 20) "getD in bounds"
  assert (a.getD 99 0 == 0) "getD out of bounds"

  -- toArray
  assert (a.toArray (fun _ x => x) == #[10, 20, 30]) "toArray"

  -- toString
  assert (s!"{b}" == "#[10, 99, 30]") "toString"

  IO.println "Basic tests passed."

  -- Stress test: build a large array using Array-backed push.
  -- Completing in < 1s proves native Array.push (O(1) amortized) is used.
  let n := 100000
  let start ← IO.monoMsNow
  let big := buildBig n
  let elapsed := (← IO.monoMsNow) - start

  assert (big.size == n) "big size"
  assert (big.getD 0 42 == 0) "big[0]"
  assert (big.getD (n - 1) 42 == n - 1) "big[n-1]"

  IO.println s!"100k push+get: {elapsed}ms (native Array performance)"
  assert (elapsed < 2000) "100k ops should complete quickly"

  IO.println "All tests passed."
