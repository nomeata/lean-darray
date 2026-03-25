import DArray.Structure

/-! # Benchmark: `large_structure` scaling with field count

Generates homogeneous structures at various sizes and measures
construct / get-all / set-all times to verify linear scaling.
-/

open Lean in
/-- Generate a `large_structure` with `N` fields all of type `Nat`,
    named `f0` through `f{N-1}`. Only used in this benchmark. -/
local macro "large_homo_structure " name:ident n:num : command => do
  let nVal := n.getNat
  if nVal == 0 then
    Macro.throwError "large_homo_structure requires at least 1 field"
  let mut fields : Array (TSyntax `lsField) := #[]
  for i in [:nVal] do
    let fieldName := mkIdentFrom name (Name.mkSimple s!"f{i}")
    let natTy ← `(Nat)
    -- Construct `lsField` node manually (quotation has a parser conflict with `:`)
    let f : TSyntax `lsField := ⟨Syntax.node3 SourceInfo.none `lsFieldRule fieldName (mkAtom ":") natTy⟩
    fields := fields.push f
  `(large_structure $name where $[$fields]*)

set_option maxRecDepth 4096

-- Generate structures at various sizes
large_homo_structure S10 10
large_homo_structure S50 50
large_homo_structure S100 100
large_homo_structure S500 500
large_homo_structure S1000 1000

/-- Time an IO action in nanoseconds. -/
def timeNs (act : IO Unit) : IO Nat := do
  let t0 ← IO.monoNanosNow
  act
  let t1 ← IO.monoNanosNow
  return t1 - t0

/-- Number of iterations per benchmark to amortize overhead. -/
def iters : Nat := 1000

def benchSize (label : String) (n : Nat) : IO Unit := do
  -- All motives reduce to Nat, so we use fun _ => Nat at runtime
  let motive : Nat → Type := fun _ => Nat
  let tConstruct ← timeNs do
    for _ in [:iters] do
      let _ := DArray.ofFn (α := motive) (n := n) (fun i => i.val)
  let tGet ← timeNs do
    let r := DArray.ofFn (α := motive) (n := n) (fun i => i.val)
    for _ in [:iters] do
      for h : j in [:n] do
        let _ := r.get ⟨j, h.upper⟩
  let tSet ← timeNs do
    let r := DArray.ofFn (α := motive) (n := n) (fun i => i.val)
    for _ in [:iters] do
      let mut r' := r
      for h : j in [:n] do
        r' := r'.set ⟨j, h.upper⟩ (0 : Nat)
  IO.println s!"{label} | {tConstruct / iters} | {tGet / iters} | {tSet / iters}"

def main : IO Unit := do
  IO.println "size | construct (ns/iter) | get-all (ns/iter) | set-all (ns/iter)"
  IO.println "-----|----------------------|-------------------|-------------------"
  benchSize "  10" 10
  benchSize "  50" 50
  benchSize " 100" 100
  benchSize " 500" 500
  benchSize "1000" 1000
