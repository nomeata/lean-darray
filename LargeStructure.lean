import DArray

/-! # `large_structure` command macro

Generates a heterogeneous record type backed by `DArray` + `RArray`,
with O(log n) kernel reduction per field access.

## Usage

```
large_structure Person where
  name : String
  age : Nat
  active : Bool
```

Generates `_Types`, `_Motive`, the `def` alias, a `mk` constructor,
and per-field `get`/`set`/`modify` accessors in a namespace.
-/

open Lean (RArray)

/-- Build balanced `RArray` syntax from an array of type syntaxes.
    Mirrors `RArray.ofFn.go`: split at `mid = (lb + ub) / 2`. -/
private partial def mkRArraySyntax (types : Array (Lean.TSyntax `term)) (lb ub : Nat) :
    Lean.MacroM (Lean.TSyntax `term) := do
  if ub - lb == 1 then
    let ty := types[lb]!
    `(Lean.RArray.leaf $ty)
  else
    let mid := (lb + ub) / 2
    let left ← mkRArraySyntax types lb mid
    let right ← mkRArraySyntax types mid ub
    let midLit := Lean.Syntax.mkNumLit (toString mid)
    `(Lean.RArray.branch $midLit $left $right)

declare_syntax_cat lsField
syntax ident " : " term:max : lsField

syntax "large_structure " ident " where" (ppLine colGe lsField)* : command

macro_rules
  | `(large_structure $name where $[$fields:lsField]*) => do
    -- Parse fields
    let fieldData ← fields.mapM fun f => do
      match f with
      | `(lsField| $n:ident : $t:term) => pure (n, t)
      | _ => Lean.Macro.throwError "invalid field syntax"
    if fieldData.isEmpty then
      Lean.Macro.throwError "large_structure requires at least one field"
    let n := fieldData.size
    let nLit := Lean.Syntax.mkNumLit (toString n)

    -- Build RArray syntax tree
    let types := fieldData.map (·.2)
    let rarray ← mkRArraySyntax types 0 n

    -- Names
    let typesName := Lean.mkIdentFrom name (name.getId ++ `_Types)
    let motiveName := Lean.mkIdentFrom name (name.getId ++ `_Motive)

    -- _Types and _Motive
    let typesCmd ← `(command| private def $typesName : Lean.RArray Type := $rarray)
    let motiveCmd ← `(command| abbrev $motiveName (i : Nat) : Type := ($typesName).get i)

    -- Main def
    let mainCmd ← `(command| def $name := DArray $motiveName $nLit)

    -- Accessors
    let mut accessorCmds : Array (Lean.TSyntax `command) := #[]
    for i in [:n] do
      let (fieldName, fieldType) := fieldData[i]!
      let iLit := Lean.Syntax.mkNumLit (toString i)

      -- Capitalize first letter for setter/modifier names
      let nameStr := fieldName.getId.toString
      let chars := nameStr.toList
      let capName := String.ofList (chars.head!.toUpper :: chars.tail!)
      let setterName := Lean.mkIdentFrom fieldName (Lean.Name.mkSimple s!"set{capName}")
      let modifierName := Lean.mkIdentFrom fieldName (Lean.Name.mkSimple s!"modify{capName}")

      let getter ← `(command| def $fieldName (r : $name) : $fieldType := r.get ⟨$iLit, by omega⟩)
      let setter ← `(command| def $setterName (r : $name) (v : $fieldType) : $name := r.set ⟨$iLit, by omega⟩ v)
      let modifier ← `(command| def $modifierName (r : $name) (f : $fieldType → $fieldType) : $name := r.modify ⟨$iLit, by omega⟩ f)
      accessorCmds := accessorCmds.push getter |>.push setter |>.push modifier

    -- Constructor: def mk (f1 : T1) (f2 : T2) ... : Name :=
    --   DArray.mkEmpty n |>.push f1 |>.push f2 ...
    let mkName := Lean.mkIdentFrom name `mk
    let mut body ← `((DArray.mkEmpty $nLit : DArray $motiveName 0))
    for (fn, _) in fieldData do
      body ← `($body |>.push $fn)
    -- Build type signature: T1 → T2 → ... → Name
    let mut mkType : Lean.TSyntax `term := name
    let mut i := n
    while i > 0 do
      i := i - 1
      let (_, ft) := fieldData[i]!
      mkType ← `($ft → $mkType)
    -- Build lambda body: fun (f1 : T1) (f2 : T2) ... => pushChain
    let mut lamBody : Lean.TSyntax `term := body
    i := n
    while i > 0 do
      i := i - 1
      let (fn, ft) := fieldData[i]!
      lamBody ← `(fun ($fn : $ft) => $lamBody)
    let mkCmd ← `(command| def $mkName : $mkType := $lamBody)

    -- Wrap in namespace
    let nsOpen ← `(command| namespace $name)
    let nsClose ← `(command| end $name)

    let allCmds : Array (Lean.TSyntax `command) :=
      #[typesCmd, motiveCmd, mainCmd, nsOpen] ++ accessorCmds ++ #[mkCmd, nsClose]
    return Lean.mkNullNode (allCmds.map (·.raw))

/-! ## Inline test -/

large_structure TestPerson where
  name : String
  age : Nat
  active : Bool

/-- Verify the generated structure works at runtime. -/
def testLargeStructure : IO Unit := do
  let p := TestPerson.mk "Alice" 30 true
  assert! p.name == "Alice"
  assert! p.age == 30
  assert! p.active == true
  let p2 := p.setName "Bob" |>.modifyAge (· + 1) |>.setActive false
  assert! p2.name == "Bob"
  assert! p2.age == 31
  assert! p2.active == false
  IO.println "LargeStructure inline tests passed"

#eval testLargeStructure
