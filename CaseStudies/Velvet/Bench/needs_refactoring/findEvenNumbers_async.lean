import CaseStudies.Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    findEvenNumbers: Extract even numbers from an array of integers, preserving order.
-/

abbrev isEvenInt (x : Int) :=
  x % 2 = 0


@[grind]
def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  let l := arr.toList
  let r := result.toList
  r.Sublist l ∧
  (∀ x, x ∈ r → isEvenInt x = true) ∧
  (∀ x,
      (isEvenInt x = true → r.count x = l.count x) ∧
      (isEvenInt x = false → r.count x = 0))

section Impl
method findEvenNumbers (arr : Array Int)
  return (result : Array Int)
  ensures postcondition arr result
  do
  let mut result : Array Int := (#[] : Array Int)
  let mut i : Nat := 0
  while i < arr.size
    invariant "inv_i_bounds" (i ≤ arr.size)
    invariant "inv_sublist_prefix" (result.toList.Sublist (List.take i arr.toList))
    invariant "inv_all_even" (∀ x, x ∈ result.toList → isEvenInt x = true)
    invariant "inv_count_odds_zero" (∀ x, isEvenInt x = false → result.toList.count x = 0)
    invariant "inv_count_evens_prefix" (∀ x, isEvenInt x = true → result.toList.count x = (List.take i arr.toList).count x)
    done_with i = arr.size
  do
    let x := arr[i]!
    if isEvenInt x = true then
      result := result.push x
    i := i + 1
  return result
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct findEvenNumbers by
  ( loom_solve_async
    · -- Sublist after push
      have h_len : i < arr.toList.length := if_pos
      have h_take : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]!] :=
        by
        simp at h_len; simp [h_len]
        simpa using List.take_succ_eq_append_getElem (l := arr.toList) (i := i) h_len
      rw [h_take]
      exact List.Sublist.append invariant_inv_sublist_prefix (List.Sublist.refl _)
    · -- Count evens after push
      intro x hx
      have h_len : i < arr.toList.length := if_pos
      have h_take : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]!] := by
        simp at h_len; simp [h_len]
        simpa using List.take_succ_eq_append_getElem (l := arr.toList) (i := i) h_len
      simp [h_take, List.count_append, invariant_inv_count_evens_prefix x hx]
    · -- Count evens when skipping odd
      intro x hx
      have h_len : i < arr.toList.length := if_pos
      have h_take : List.take (i + 1) arr.toList = List.take i arr.toList ++ [arr[i]!] := by
        simp at h_len; simp [h_len]
        simpa using List.take_succ_eq_append_getElem (l := arr.toList) (i := i) h_len
      have h_ne : x ≠ arr[i]! := by intro heq; rw [heq] at hx; omega
      simp [h_take, List.count_append, invariant_inv_count_evens_prefix x hx, List.count_singleton]
      intro h_eq; rw [h_eq] at h_ne; contradiction
    · -- Final postcondition
      rcases i_2 with ⟨hi, hres⟩
      have htake : List.take i arr.toList = arr.toList := by simp [done_1]
      constructor
      · simpa [hres, htake] using invariant_inv_sublist_prefix
      constructor
      · intro x hx
        have : x ∈ result := by simp at hx; simp [hres, hx]
        simpa [hres] using invariant_inv_all_even x this
      · intro x
        constructor
        · intro hxEven
          have h : 2 ∣ x := by simpa [isEvenInt] using hxEven
          simpa [hres, htake] using invariant_inv_count_evens_prefix x h
        · intro hxOdd
          have h : x % 2 = 1 := by simp [isEvenInt] at hxOdd; omega
          simpa [hres] using invariant_inv_count_odds_zero x h)

end Proof
