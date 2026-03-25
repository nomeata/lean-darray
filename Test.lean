import DArray

set_option maxRecDepth 1024

abbrev constNat := fun (_ : Nat) => Nat

def check (name : String) (actual expected : Nat) : IO Unit := do
  if actual != expected then
    throw <| IO.userError s!"{name}: expected {expected}, got {actual}"

def main : IO Unit := do
  IO.println "=== push/get ==="
  let a := (DArray.mkEmpty 4 : DArray constNat 0).push 0 |>.push 10 |>.push 20 |>.push 30
  check "push[0]" (a.get ⟨0, by omega⟩) 0
  check "push[3]" (a.get ⟨3, by omega⟩) 30
  IO.println "  ok"

  IO.println "=== ofFn ==="
  let c := DArray.ofFn (α := constNat) (n := 4) (fun i => i.val * 10)
  check "ofFn[0]" (c.get ⟨0, by omega⟩) 0
  check "ofFn[1]" (c.get ⟨1, by omega⟩) 10
  check "ofFn[2]" (c.get ⟨2, by omega⟩) 20
  check "ofFn[3]" (c.get ⟨3, by omega⟩) 30
  IO.println "  ok"

  IO.println "=== set ==="
  let d := c.set ⟨1, by omega⟩ 99
  check "set[1]" (d.get ⟨1, by omega⟩) 99
  IO.println "  ok"

  IO.println "=== pop ==="
  let e := c.pop
  check "pop.size" e.size 3
  check "pop[0]" (e.get ⟨0, by omega⟩) 0
  IO.println "  ok"

  IO.println "=== head/back ==="
  check "head" c.head 0
  check "back" c.back 30
  IO.println "  ok"

  IO.println "=== modify ==="
  let m := c.modify ⟨2, by omega⟩ (· + 5)
  check "modify[2]" (m.get ⟨2, by omega⟩) 25
  IO.println "  ok"

  IO.println "=== map ==="
  let f := c.map (fun _ x => x + 1)
  check "map[0]" (f.get ⟨0, by omega⟩) 1
  check "map[1]" (f.get ⟨1, by omega⟩) 11
  IO.println "  ok"

  IO.println "=== replicate ==="
  let g := DArray.replicate 3 42
  check "replicate[0]" (g.get ⟨0, by omega⟩) 42
  IO.println "  ok"

  IO.println "=== take ==="
  let t := c.take 2 (by omega)
  check "take.size" t.size 2
  check "take[0]" (t.get ⟨0, by omega⟩) 0
  IO.println "  ok"

  IO.println "=== foldl ==="
  let sum := c.foldl (fun _ acc x => acc + x) 0
  check "foldl" sum 60
  IO.println "  ok"

  IO.println "=== reverse ==="
  let r := c.reverse
  check "reverse[0]" (r.get ⟨0, by omega⟩) 30
  check "reverse[3]" (r.get ⟨3, by omega⟩) 0
  IO.println "  ok"

  IO.println "=== zipWith ==="
  let b := DArray.ofFn (α := constNat) (n := 4) (fun i => i.val + 1)
  let z := c.zipWith b (fun _ x y => x + y)
  check "zip[0]" (z.get ⟨0, by omega⟩) 1
  check "zip[3]" (z.get ⟨3, by omega⟩) 34
  IO.println "  ok"

  IO.println "=== append ==="
  let a1 := DArray.ofFn (α := constNat) (n := 2) (fun i => i.val)
  let a2 := DArray.ofFn (α := constNat) (n := 2) (fun i => i.val + 10)
  let ap := a1.append a2
  check "append[0]" (ap.get ⟨0, by omega⟩) 0
  check "append[2]" (ap.get ⟨2, by omega⟩) 10
  IO.println "  ok"

  IO.println "=== BEq ==="
  let c2 := DArray.ofFn (α := constNat) (n := 4) (fun i => i.val * 10)
  assert! c == c2
  IO.println "  ok"

  IO.println "=== mapM ==="
  let doubled ← c.mapM (fun _ x => pure (x * 2))
  check "mapM[1]" (doubled.get ⟨1, by omega⟩) 20
  IO.println "  ok"

  IO.println "=== foldlM ==="
  let sumM ← c.foldlM (fun _ acc x => pure (acc + x)) 0
  check "foldlM" sumM 60
  IO.println "  ok"

  IO.println "=== forM ==="
  let ref ← IO.mkRef (0 : Nat)
  c.forM (fun _ x => ref.modify (· + x))
  let forMSum ← ref.get
  check "forM" forMSum 60
  IO.println "  ok"

  IO.println "=== drop ==="
  let dr := c.drop 1 (by omega)
  check "drop[0]" (dr.get ⟨0, by omega⟩) 10
  check "drop[1]" (dr.get ⟨1, by omega⟩) 20
  check "drop.size" dr.size 3
  IO.println "  ok"

  IO.println "=== extract ==="
  let ex := c.extract 1 3 (by omega) (by omega)
  check "extract[0]" (ex.get ⟨0, by omega⟩) 10
  check "extract[1]" (ex.get ⟨1, by omega⟩) 20
  check "extract.size" ex.size 2
  IO.println "  ok"

  IO.println "=== stress ==="
  let big := DArray.ofFn (α := fun _ => Nat) (n := 100000) (fun i => i.val)
  check "big[0]" (big.get ⟨0, by omega⟩) 0
  check "big[99999]" (big.get ⟨99999, by omega⟩) 99999
  check "big.size" big.size 100000
  let bigSum := big.foldl (fun _ acc x => acc + x) 0
  check "bigSum" bigSum 4999950000
  IO.println s!"  size={big.size} sum={bigSum}"

  IO.println "all tests passed!"
