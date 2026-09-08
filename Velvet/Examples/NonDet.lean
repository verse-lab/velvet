module

public import Velvet
public meta import Velvet

open Std.WP Lean.Order

namespace Velvet.Examples.NonDet

/-- Demonic extraction preserves triples for every exceptional postcondition,
including both partial- and total-correctness endpoints. -/
example {α : Type} (s : DemonicT Option α) (pre : Prop)
    (post : α → Prop) (epost : Unit → Prop) (h : Triple s pre post epost) :
    Triple s.run pre post epost := by
  exact Soundness.DemonicChoice.ExtractNonDet.extract_refines h

/- ============================================================================
   1. Basic Demonic Choice (`DemonicT Option`)
   ============================================================================ -/

method pickGreater (inp : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures res > inp + 10
do
  let (ans : Nat) :| ans > inp + 200
  return ans

prove_correct pickGreater by
  velvet_vcgen [pickGreater]
  case signals1 =>
    rename_i inp hnone
    exact hnone ⟨inp + 201, by omega⟩
  case ensures1 => grind

/-- Extraction evaluates the choice constructively using `findNat`: `10 + 200 = 210` -> `some 211`. -/
example : (pickGreater 10).run = some 211 := by native_decide

/-- Non-deterministic choice specifying an explicit finder via `using`. -/
method pickWithCustomHint (inp : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures res = inp + 42
do
  let (ans : Nat) :| ans = inp + 42 using (Findable.ofFn (fun _ => some (inp + 42)) (by simp) (by rintro _ ⟨⟩; rfl))
  return ans

prove_correct pickWithCustomHint by
  velvet_vcgen [pickWithCustomHint] with finish

example : (pickWithCustomHint 10).run = some 52 := by native_decide

/-- Non-deterministic choice specifying an explicit `Findable` instance via `using`. -/
method pickWithExplicitInstance (inp : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures res = inp + 1
do
  let (ans : Nat) :| ans = inp + 1 using (inferInstanceAs (Findable (fun a => a = inp + 1)))
  return ans

prove_correct pickWithExplicitInstance by
  velvet_vcgen [pickWithExplicitInstance] with finish

example : (pickWithExplicitInstance 10).run = some 11 := by native_decide

-- Multiple consecutive non-deterministic choices in sequence.
method pickTwoSum (target : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures ensures_sum : res = target + 5
do
  let (a : Nat) :| a = target
  let (b : Nat) :| b = 5
  return a + b

prove_correct pickTwoSum by
  velvet_vcgen [pickTwoSum]
  case signals1 =>
    rename_i target hnone
    exact hnone ⟨target, rfl⟩
  case signals1 =>
    have : ∃ b : Nat, b = 5 := ⟨5, rfl⟩
    contradiction
  case ensures_sum => grind

example : (pickTwoSum 10).run = some 15 := by native_decide

-- Demonic choice combined with `NonDetT.assume`.
method pickDemonicWithAssume (n : Nat) returns (res : Nat) in DemonicT Option
  requires n_pos : n > 0
  signals (_ : Unit) => False
  ensures ensures_bound : res ≥ n
do
  let (x : Nat) :| x ≥ n
  assume' (x ≥ n)
  return x

prove_correct pickDemonicWithAssume by
  velvet_vcgen [pickDemonicWithAssume]
  case signals1 =>
    rename_i n hnone
    exact hnone ⟨n, Nat.le_refl n⟩
  case signals1 =>
    rename_i n x hnone
    exact hnone x.property
  case ensures_bound => grind

example : (pickDemonicWithAssume 7).run = some 7 := by native_decide

-- Conditional non-deterministic choice based on branching control flow.
method pickBranch (flag : Bool) (x : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures branch_true : flag = true → res > x
  ensures branch_false : flag = false → res = 0
do
  if flag then
    let (y : Nat) :| y > x + 10
    return y
  else
    return 0

prove_correct pickBranch by
  velvet_vcgen [pickBranch]
  case signals1 =>
    rename_i flag x hnone
    exact hnone ⟨x + 11, by omega⟩
  case branch_true => grind
  case branch_false => grind
  case branch_true => grind
  case branch_false => grind

example : (pickBranch true 5).run = some 16 := by native_decide
example : (pickBranch false 5).run = some 0 := by native_decide

/- ============================================================================
   2. Finite Domain Search (`Finitary`)
   ============================================================================ -/

method pickSquare (n : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures res * res = 16
do
  let (x : Fin 10) :| x.val * x.val = 16
  return x.val

prove_correct pickSquare by
  velvet_vcgen [pickSquare]
  case signals1 =>
    have : ∃ x : Fin 10, x.val * x.val = 16 := ⟨4, by decide⟩
    contradiction
  case ensures1 => grind

example : (pickSquare 0).run = some 4 := by native_decide

/- ============================================================================
   3. Loops in Demonic Non-Determinism (`DemonicT Option`)
   ============================================================================ -/

method loopDemonic (n : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures res = n
do
  let mut i : Nat := 0
  while' loop_cond : i < n
    invariant inv_i : i ≤ n
    decreasing by_rem : n - i
    done_with h_done : i = n
  do
    i := i + 1
  return i

prove_correct loopDemonic by
  velvet_vcgen [loopDemonic]
  case inv_i => grind
  case inv_i => grind
  case inv_i => grind
  case by_rem => grind
  case h_done => grind
  case ensures1 => grind


example : (loopDemonic 5).run = some 5 := by native_decide

/-- A loop with non-deterministic choice inside the loop body. -/
method loopWithChoice (n : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures res ≥ n
do
  let mut i : Nat := 0
  while' loop_cond : i < n
    invariant inv_i : i ≤ n
    decreasing by_rem : n - i
    done_with h_done : i = n
  do
    let (step : Nat) :| step = 1
    i := i + step
  return i

prove_correct loopWithChoice by
  velvet_vcgen [loopWithChoice] with finish

example : (loopWithChoice 10).run = some 10 := by native_decide

/-- A bounded accumulator loop choosing step sizes ≤ 2 non-deterministically. -/
method loopAccum (n : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures res ≤ n * 2
do
  let mut cur : Nat := 0
  let mut i : Nat := 0
  while' loop_cond : i < n
    invariant inv_i : i ≤ n ∧ cur ≤ i * 2
    decreasing by_rem : n - i
    done_with h_done : i = n
  do
    let (step : Nat) :| step ≤ 2
    cur := cur + step
    i := i + 1
  return cur

prove_correct loopAccum by
  velvet_vcgen [loopAccum]
  case signals1 =>
    have : ∃ step : Nat, step ≤ 2 := ⟨0, by omega⟩
    contradiction
  all_goals grind

example : (loopAccum 5).run = some 0 := by native_decide

/- ============================================================================
   4. Angelic Non-Determinism (`AngelicT Option`)
   ============================================================================ -/

/-- An angelic program choosing a boolean witness. -/
method pickAngelic (n : Nat) returns (res : Nat) in AngelicT Option
  signals (_ : Unit) => False
  ensures res > n
do
  let (b : Bool) :| b = true
  return n + 1

prove_correct pickAngelic by
  velvet_vcgen [pickAngelic] with try finish

example : (pickAngelic 10).run = some 11 := by native_decide

/-- An angelic program choosing a positive natural increment. -/
method pickAngelicChoice (n : Nat) returns (res : Nat) in AngelicT Option
  signals (_ : Unit) => False
  ensures res > n
do
  let (diff : Nat) :| diff > 0
  return n + diff

prove_correct pickAngelicChoice by
  velvet_vcgen [pickAngelicChoice] with try finish
  case diff => exact Nat.zero_lt_one

example : (pickAngelicChoice 10).run = some 11 := by native_decide

/-- Synthesizing a non-trivial factor of 10 angelically. -/
method findDivisor (n : Nat) returns (d : Nat) in AngelicT Option
  signals (_ : Unit) => False
  ensures d > 1 ∧ d < 10 ∧ 10 % d = 0
do
  let (cand : Nat) :| cand > 1 ∧ cand < 10 ∧ 10 % cand = 0
  return cand

prove_correct findDivisor by
  velvet_vcgen [findDivisor] with try finish
  case vc3 => exact 2
  case cand => decide

example : (findDivisor 10).run = some 2 := by native_decide

/-- A `while'` loop executing within `AngelicT Option` with non-deterministic choice
inside the loop body. -/
method loopAngelic (n : Nat) returns (res : Nat) in AngelicT Option
  signals (_ : Unit) => False
  ensures res = n
do
  let mut i : Nat := 0
  while' loop_cond : i < n
    invariant inv_i : i ≤ n
    decreasing by_rem : n - i
    done_with h_done : i = n
  do
    let (step : Nat) :| step = 1
    i := i + step
  return i

prove_correct loopAngelic by
  velvet_vcgen [loopAngelic] with try finish

example : (loopAngelic 5).run = some 5 := by native_decide

/- ============================================================================
   5. Stateful Non-Determinism (`DemonicT (StateT σ Option)`)
   ============================================================================ -/

def incCounter : DemonicT (StateT Nat Option) Nat := do
  let s ← monadLift (get : StateT Nat Option Nat)
  let (step : Nat) :| step ≥ 1
  monadLift (set (s + step) : StateT Nat Option PUnit)
  return s + step

example : (incCounter.run 10) = some (11, 11) := by native_decide

method pickNegativeInt (target : Int) returns (res : Int) in DemonicT Option
  signals (_ : Unit) => False
  ensures bound : res < target
do
  let (z : Int) :| z < target
  return z

prove_correct pickNegativeInt by
  velvet_vcgen [pickNegativeInt]
  case signals1 =>
    rename_i target hnone
    exact hnone ⟨target - 1, by omega⟩
  case bound => grind

example : (pickNegativeInt (-5)).run = some (-6) := by native_decide
example : (pickNegativeInt 3).run = some 0 := by native_decide

/-- Non-deterministic interval contraction:
A loop repeatedly contracts `[low, high]` by picking an arbitrary partition point `mid`
in `[low, high)` and updating `low := mid + 1`.
Stresses termination with variable non-deterministic strides.
All loop VCs verified with explicit `case` proofs using `grind`. -/
method bisectDemonic (high : Nat) returns (res : Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures bounds_equal : res = high
do
  let mut low : Nat := 0
  while' loop_cond : low < high
    invariant inv_bounds : low ≤ high
    decreasing by_rem : high - low
    done_with h_done : low = high
  do
    let (mid : Nat) :| low ≤ mid ∧ mid < high
    low := mid + 1
  return low

prove_correct bisectDemonic by
  velvet_vcgen [bisectDemonic]
  case signals1 =>
    rename_i high hnone
    exact hnone ⟨low, by omega⟩
  case inv_bounds => grind
  case bounds_equal => grind
  case by_rem => grind
  case inv_bounds => grind
  case inv_bounds => grind
  case h_done => grind

example : (bisectDemonic 10).run = some 10 := by native_decide

/-- Non-deterministic 2D Manhattan grid walk:
Starting from `(0, 0)`, in each step the system nondeterministically chooses
a directional step from `Fin 2 × Fin 2` such that `dx + dy = 1`.
Because `Fin 2 × Fin 2` has a `Finitary` instance, it evaluates constructively at runtime! -/
method gridWalk (n : Nat) returns (pos : Nat × Nat) in DemonicT Option
  signals (_ : Unit) => False
  ensures total_dist : pos.1 + pos.2 = n
do
  let mut x : Nat := 0
  let mut y : Nat := 0
  let mut i : Nat := 0
  while' loop_cond : i < n
    invariant inv_diag : x + y = i ∧ i ≤ n
    decreasing by_rem : n - i
    done_with h_done : i = n
  do
    let (step : Fin 2 × Fin 2) :| step.1.val + step.2.val = 1
    x := x + step.1.val
    y := y + step.2.val
    i := i + 1
  return (x, y)

prove_correct gridWalk by
  velvet_vcgen [gridWalk]
  case signals1 =>
    have : ∃ step : Fin 2 × Fin 2,
        step.1.val + step.2.val = 1 := ⟨(0, 1), by decide⟩
    contradiction
  case inv_diag => grind
  case total_dist => grind
  case by_rem => grind
  case inv_diag => grind
  case inv_diag => grind
  case h_done => grind

example : (gridWalk 5).run = some (0, 5) := by native_decide

public structure TokenState where
  spent : Nat
  remaining : Nat
  deriving Repr, DecidableEq

/-- Non-deterministic Token Allocator:
Given an initial budget `capacity`, a consumer nondeterministically demands a
batch `req` with `1 ≤ req ∧ req ≤ rem` in each iteration until the budget is exhausted.
Maintains the conservation invariant `spent + rem = capacity`. -/
method allocateTokens (capacity : Nat) returns (res : TokenState) in DemonicT Option
  signals (_ : Unit) => False
  ensures conservation : res.spent + res.remaining = capacity
  ensures exhausted : res.remaining = 0
do
  let mut rem : Nat := capacity
  let mut spent : Nat := 0
  while' loop_cond : rem > 0
    invariant inv_budget : spent + rem = capacity
    decreasing by_rem : rem
    done_with h_done : rem = 0
  do
    let (req : Nat) :| 1 ≤ req ∧ req ≤ rem
    rem := rem - req
    spent := spent + req
  return ⟨spent, rem⟩

prove_correct allocateTokens by
  velvet_vcgen [allocateTokens]
  case signals1 =>
    have : ∃ req, 1 ≤ req ∧ req ≤ rem := ⟨1, by omega⟩
    contradiction
  case inv_budget => grind
  case conservation => grind
  case exhausted => grind
  case by_rem => grind
  case inv_budget => grind
  case inv_budget => grind
  case h_done => grind

example : (allocateTokens 10).run = some ⟨10, 0⟩ := by native_decide

public structure PartitionLists where
  pivot : Nat
  left : List Nat
  right : List Nat
  deriving Repr, DecidableEq

/-- Quicksort Partition Step with Nondeterministic Pivot:
Nondeterministically picks a pivot index `idx < xs.length`, reads `pivot := xs[idx]!`,
and partitions `xs` into sublists `left` and `right`.
Stresses:
- Array/List indexing with non-deterministic index selection
- Dual list accumulators
- Universal quantifications over dynamic sublists in loop invariants
- Discharges all 23 VCs with explicit `case <name> => grind` proofs! -/
method partitionLists (xs : List Nat) returns (res : PartitionLists) in DemonicT Option
  requires h_len : xs.length > 0
  signals (_ : Unit) => False
  ensures pivot_in_list : res.pivot ∈ xs
  ensures left_le : ∀ x ∈ res.left, x ≤ res.pivot
  ensures right_gt : ∀ x ∈ res.right, x > res.pivot
  ensures total_len : res.left.length + res.right.length = xs.length
do
  let (idx : Nat) :| idx < xs.length
  let pivot := xs[idx]!
  let mut left : List Nat := []
  let mut right : List Nat := []
  let mut i : Nat := 0
  while' loop_cond : i < xs.length
    invariant inv_i : i ≤ xs.length
    invariant inv_left : ∀ x ∈ left, x ≤ pivot
    invariant inv_right : ∀ x ∈ right, x > pivot
    invariant inv_len : left.length + right.length = i
    decreasing by_rem : xs.length - i
    done_with h_done : i = xs.length
  do
    if xs[i]! ≤ pivot then
      left := xs[i]! :: left
    else
      right := xs[i]! :: right
    i := i + 1
  return ⟨pivot, left, right⟩

prove_correct partitionLists by
  velvet_vcgen [partitionLists]
  case signals1 =>
    rename_i xs hnone
    exact hnone ⟨0, h_len⟩
  case inv_i => grind
  case inv_left => grind
  case inv_right => grind
  case inv_len => grind
  case pivot_in_list => grind
  case left_le => grind
  case right_gt => grind
  case total_len => grind
  case by_rem => grind
  case inv_i => grind
  case inv_left => grind
  case inv_right => grind
  case inv_len => grind
  case by_rem => grind
  case inv_i => grind
  case inv_left => grind
  case inv_right => grind
  case inv_len => grind
  case inv_i => grind
  case inv_left => grind
  case inv_right => grind
  case inv_len => grind
  case h_done => grind

example : (partitionLists [5, 2, 8, 1, 9, 3]).run = some ⟨5, [3, 1, 2, 5], [9, 8]⟩ := by native_decide

end Velvet.Examples.NonDet
