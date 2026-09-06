module

prelude
public import Lean
public import Init.Data.Nat.Basic
public import Init.Data.Int.Basic
public import Init.Data.Array.Basic
public import Init.Data.List.Basic
public import Init.Data.String.Basic

namespace Velvet.Testing

/-- Typeclass providing random test generation for values of type `α`.
`sample size` produces a randomized value scaled up to roughly `size`. -/
public class Sampleable (α : Type) where
  sample : (size : Nat) → IO α

public instance : Sampleable Nat where
  sample size := IO.rand 0 (size + 1)

public instance : Sampleable Int where
  sample size := do
    let n ← IO.rand 0 (size + 1)
    let s ← IO.rand 0 1
    return if s == 0 then (n : Int) else -(n : Int)

public instance : Sampleable Bool where
  sample _ := do
    let b ← IO.rand 0 1
    return b == 1

public instance : Sampleable Char where
  sample _ := do
    let code ← IO.rand 97 122  -- 'a' .. 'z'
    return Char.ofNat code

public instance : Sampleable String where
  sample size := do
    let len ← IO.rand 0 (size.min 15 + 1)
    let mut chars := #[]
    for _ in [0:len] do
      chars := chars.push (← Sampleable.sample (α := Char) size)
    return String.ofList chars.toList

public instance [Sampleable α] : Sampleable (Array α) where
  sample size := do
    let len ← IO.rand 0 (size.min 20 + 1)
    let mut arr := #[]
    for _ in [0:len] do
      let x ← Sampleable.sample (α := α) size
      arr := arr.push x
    return arr

public instance [Sampleable α] : Sampleable (List α) where
  sample size := do
    let arr ← Sampleable.sample (α := Array α) size
    return arr.toList

public instance [Sampleable α] : Sampleable (Option α) where
  sample size := do
    let isSome ← IO.rand 0 3
    if isSome == 0 then return none
    else return some (← Sampleable.sample (α := α) size)

public instance [Sampleable α] [Sampleable β] : Sampleable (α × β) where
  sample size := do
    let a ← Sampleable.sample (α := α) size
    let b ← Sampleable.sample (α := β) size
    return (a, b)

public instance [Sampleable α] [Sampleable β] : Sampleable (α ⊕ β) where
  sample size := do
    let pick ← IO.rand 0 1
    if pick == 0 then
      return Sum.inl (← Sampleable.sample (α := α) size)
    else
      return Sum.inr (← Sampleable.sample (α := β) size)

public instance {n : Nat} [NeZero n] : Sampleable (Fin n) where
  sample _ := do
    let v ← IO.rand 0 (n - 1)
    if h : v < n then
      return ⟨v, h⟩
    else
      return ⟨0, Nat.pos_of_ne_zero NeZero.out⟩

/-- Typeclass for testable properties.
Recursively decomposes curried functions `α → β → ... → Bool` by sampling
arguments using `[Sampleable α]` and displaying counterexamples. -/
public class TestableProp (p : Type) where
  runTest : p → (size : Nat) → IO (Option String)

public instance : TestableProp Bool where
  runTest b _ := return if b then none else some "postcondition or predicate evaluated to false"

public instance [Sampleable α] [ToString α] [TestableProp β] : TestableProp (α → β) where
  runTest f size := do
    let x ← Sampleable.sample (α := α) size
    let subRes ← TestableProp.runTest (f x) size
    match subRes with
    | none => return none
    | some msg => return some s!"{x} ⊢ {msg}"

/-- Test runner configuration. -/
public structure TestConfig where
  numTests : Nat := 100
  maxSize : Nat := 50
deriving Inhabited

/-- Run property-based tests on `prop` with `numTests` iterations and inputs up to `maxSize`.
Prints progress and reports any failing counterexample. -/
public def velvetQuickCheck {p : Type} [TestableProp p]
    (name : String) (prop : p) (numTests : Nat := 100) (maxSize : Nat := 50) : IO Bool := do
  for i in [1:numTests + 1] do
    let size := (i * maxSize) / numTests + 1
    let res ← TestableProp.runTest prop size
    if let some ce := res then
      IO.println s!"[Velvet PBT] Counterexample found for `{name}` on test #{i}:"
      IO.println s!"  {ce}"
      return false
  IO.println s!"[Velvet PBT] Passed {numTests} tests for `{name}`."
  return true

end Velvet.Testing
