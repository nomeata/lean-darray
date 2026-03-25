# DArray

A dependent array for Lean 4 where the element at index `i` has type `α i`, backed by a native `Array` at runtime.

## What is DArray?

`DArray (α : Nat → Type u) (n : Nat)` is a length-indexed array whose element type can depend on the index. For example, you can have an array where position 0 holds a `String`, position 1 holds a `Nat`, etc.

At runtime, `DArray` is represented as a plain `Array` using `@[implemented_by]` — so you get full dependent typing at the logical level with native array performance at runtime.

## Installation

Add to your `lakefile.toml`:

```toml
[[require]]
name = "darray"
git = "https://github.com/nomeata/lean-darray"
rev = "main"
```

Then `import DArray` in your Lean files.

## Usage

### Constant type family (like Vector)

```lean
import DArray

-- All elements have type Nat
abbrev constNat := fun (_ : Nat) => Nat

-- Build from a function
def myArr := DArray.ofFn (α := constNat) (n := 4) (fun i => i.val * 10)
-- myArr contains [0, 10, 20, 30]

-- Build incrementally
def myArr2 := (DArray.mkEmpty 4 : DArray constNat 0).push 0 |>.push 10 |>.push 20 |>.push 30

-- Access elements (index is Fin n)
#eval myArr.get ⟨2, by omega⟩  -- 20
#eval myArr.head                -- 0
#eval myArr.back                -- 30
```

### Truly dependent type family

```lean
import DArray

-- Position 0 holds a Nat, position 1 holds a String
def myTypes : Nat → Type
  | 0 => Nat
  | 1 => String
  | _ => Unit

def hetArr := (DArray.mkEmpty 2 : DArray myTypes 0).push (42 : Nat) |>.push ("hello" : String)
```

## API Overview

### Construction
| Operation | Description |
|-----------|-------------|
| `mkEmpty` | Empty array with capacity hint |
| `empty` | Empty array |
| `ofFn` | Create from a function `Fin n → α i` |
| `singleton` | Single-element array |
| `replicate` | `n` copies of the same value |

### Element access
| Operation | Description |
|-----------|-------------|
| `get` | Get element at index (Fin n) |
| `getD` | Get with default for out-of-bounds |
| `head` | First element |
| `back` | Last element |
| `size` | Number of elements |
| `isEmpty` | Check if empty |

### Modification
| Operation | Description |
|-----------|-------------|
| `set` | Set element at index |
| `setIfInBounds` | Set if index is in bounds |
| `modify` | Apply function to element at index |
| `push` | Append element |
| `pop` | Remove last element |

### Transformation
| Operation | Description |
|-----------|-------------|
| `map` | Map function over elements |
| `mapM` | Monadic map |
| `reverse` | Reverse the array |
| `take` / `shrink` | First k elements |
| `drop` | Drop first k elements |
| `extract` | Subrange [start, stop) |
| `append` | Concatenate two arrays |
| `zipWith` / `zip` | Combine two arrays element-wise |
| `cast` | Change size with proof of equality |

### Iteration
| Operation | Description |
|-----------|-------------|
| `foldl` / `foldlM` | Left fold |
| `foldr` / `foldrM` | Right fold |
| `forM` | Monadic iteration |
| `forIn` | Iteration with early termination |
| `any` / `anyM` | Check if any element satisfies predicate |
| `all` / `allM` | Check if all elements satisfy predicate |
| `findIdx?` | Find first index satisfying predicate |
| `findSome?` | Find first `some` result |
| `toArray` / `toList` | Convert by mapping elements |

### Instances
`BEq`, `DecidableEq`, `Inhabited`, `Repr`, `ToString`

## Implementation

`DArray` is defined as a structure wrapping a dependent function:

```lean
structure DArray (α : Nat → Type u) (n : Nat) where
  private mk ::
  private fn : (i : Fin n) → α i
```

Every operation has two definitions:
1. A **logical definition** using the function representation (for proofs)
2. An **unsafe implementation** using `Array` with `unsafeCast` (for performance)

The `@[implemented_by]` attribute redirects compiled code to the unsafe implementation. This is sound because all boxed Lean types share the same runtime representation (`lean_object*`).

Core operations are marked `@[noinline]` to ensure the compiler uses the `@[implemented_by]` implementations rather than inlining the logical definitions.

## License

Apache 2.0 — see [LICENSE](LICENSE).
