import CaseStudies.TestingUtil
import Loom.MonadAlgebras.WP.Attr

set_option linter.unusedTactic false

example (arr: Array Int) (target: Int) (res: Int) :
  Decidable
    (res = -1 → (∀ (i : Nat), 0 ≤ i ∧ i < arr.size → arr[i]! ≠ target))
  := by infer_aux_decidable_instance ; infer_instance

example (arr: Array Int) (target: Int) (res: Int) :
  Decidable
    (res ≠ -1 → (0 ≤ res ∧ res < arr.size ∧ (arr[res.toNat]! = target) ∧ (∀ (k : Nat), 0 ≤ k ∧ k < res.toNat → arr[k]! ≠ target)))
  := by infer_aux_decidable_instance ; infer_instance

example (arr: Array Nat) (res: Bool) :
  Decidable
    (res = true → (∀ i, 0 ≤ i ∧ i < arr.size - 1 → arr[i]! ≤ arr[i+1]!))
  := by infer_aux_decidable_instance ; infer_instance

example (arr: Array Nat) (res: Bool) :
  Decidable
    (res = false → (∃ i, 0 ≤ i ∧ i < arr.size - 1 ∧ arr[i]! > arr[i+1]!))
  := by infer_aux_decidable_instance ; infer_instance

example (arr: Array Int) :
  Decidable
    (∀ (i : Nat), 0 ≤ i → ∀ (j : Nat), i ≤ j ∧ j < arr.size → arr[i]! ≤ arr[j]!)
  := by infer_aux_decidable_instance ; infer_instance

example (arr: Array Int) :
  Decidable
    (∀ (j : Nat), j < arr.size → ∀ (i : Nat), i ≤ j → arr[i]! ≤ arr[j]!)
  := by infer_aux_decidable_instance ; infer_instance

example (f : Int → Bool) :
  Decidable
    (∀ (i : Int), -100 ≤ i →
      ∃ (b : Bool), (∀ (j : Int), i ≤ j → j ≤ 100 → (f i = b → f j = !b)))
  := by infer_aux_decidable_instance ; infer_instance
