module

public import Velvet
public meta import Velvet

/-!
## Program description

Given an array `arr` of natural numbers and an array `queries` where
`queries[i] = [left_i, right_i]`, compute the XOR of elements from `left_i` to
`right_i` for each query.

The program is expected to run in O(n + q) time and O(n) extra space, excluding the returned array.
-/

namespace XORQueriesOfASubarray

section Specs

public def subarray (arr : Array Nat) (l : Nat) (r : Nat) : Array Nat :=
  arr.extract l (r + 1)

public def xorAll (a : Array Nat) : Nat :=
  a.foldl (fun acc x => acc ^^^ x) 0

public def subarrayXor (arr : Array Nat) (l : Nat) (r : Nat) : Nat :=
  xorAll (subarray arr l r)

public def precondition (arr : Array Nat) (queries : Array (Nat × Nat)) : Prop :=
  ∀ (i : Nat), i < queries.size →
    let q := queries[i]!
    let l := q.1
    let r := q.2
    l ≤ r ∧ r < arr.size

public def postcondition (arr : Array Nat) (queries : Array (Nat × Nat)) (answer : Array Nat) : Prop :=
  answer.size = queries.size ∧
  ∀ (i : Nat), i < queries.size →
    let q := queries[i]!
    let l := q.1
    let r := q.2
    answer[i]! = subarrayXor arr l r

end Specs

section Implementation

method xorQueries (arr : Array Nat) (queries : Array (Nat × Nat))
  returns (answer : Array Nat)
  requires valid_queries: precondition arr queries
  ensures correct_answer: postcondition arr queries answer
do
  let mut pref : Array Nat := Array.replicate (arr.size + 1) 0
  let mut i : Nat := 0
  while' building_pref: i < arr.size
    invariant pref_size: pref.size = arr.size + 1
    invariant pref_i_bounds: i ≤ arr.size
    invariant pref_correct_prefix: ∀ k : Nat, k ≤ i → pref[k]! = xorAll (arr.extract 0 k)
    decreasing pref_remaining: arr.size - i
    done_with pref_done: i = arr.size
  do
    let prev := pref[i]!
    let next := prev ^^^ arr[i]!
    pref := pref.set! (i + 1) next
    i := i + 1

  let mut ans : Array Nat := Array.replicate queries.size 0
  let mut j : Nat := 0
  while' answering: j < queries.size
    invariant ans_size: ans.size = queries.size
    invariant ans_j_bounds: j ≤ queries.size
    invariant ans_correct_prefix:
      ∀ k : Nat, k < j →
        let q := queries[k]!
        let l := q.1
        let r := q.2
        ans[k]! = subarrayXor arr l r
    decreasing ans_remaining: queries.size - j
    done_with ans_done: j = queries.size
  do
    let q := queries[j]!
    let l := q.1
    let r := q.2
    let xr := pref[r + 1]!
    let xl := pref[l]!
    ans := ans.set! j (xr ^^^ xl)
    j := j + 1

  return ans

end Implementation

section Proof

theorem getElem!_set!_eq (a : Array Nat) (i v : Nat) (hi : i < a.size) :
    (a.set! i v)[i]! = v := by
  simp [Array.set!, Array.setIfInBounds, hi, getElem!_pos]

theorem getElem!_set!_ne (a : Array Nat) (i j v : Nat) (hi : i < a.size) (hj : j < a.size) (h : j ≠ i) :
    (a.set! i v)[j]! = a[j]! := by
  rw [getElem!_pos _ _ (by simpa [Array.size_set!])]
  rw [getElem!_pos a j hj]
  simp only [Array.set!, Array.setIfInBounds, dite_eq_left hi]
  exact Array.getElem_set_ne hi hj (fun heq => h heq.symm)

theorem foldl_xor_init (xs : List Nat) (a : Nat) :
    xs.foldl (fun acc x => acc ^^^ x) a = a ^^^ xs.foldl (fun acc x => acc ^^^ x) 0 := by
  induction xs generalizing a with
  | nil => simp
  | cons x tl ih =>
    have hx : List.foldl (fun acc x => acc ^^^ x) x tl = x ^^^ List.foldl (fun acc x => acc ^^^ x) 0 tl := by
      simp [ih (a := x)]
    calc
      List.foldl (fun acc x => acc ^^^ x) a (x :: tl) = List.foldl (fun acc x => acc ^^^ x) (a ^^^ x) tl := by simp [List.foldl]
      _ = (a ^^^ x) ^^^ List.foldl (fun acc x => acc ^^^ x) 0 tl := by simp [ih (a := a ^^^ x)]
      _ = a ^^^ (x ^^^ List.foldl (fun acc x => acc ^^^ x) 0 tl) := by simp [Nat.xor_assoc]
      _ = a ^^^ List.foldl (fun acc x => acc ^^^ x) x tl := by simp [hx]
      _ = a ^^^ List.foldl (fun acc x => acc ^^^ x) 0 (x :: tl) := by
            simp [List.foldl, Nat.zero_xor]

theorem xorAll_append (xs ys : Array Nat) :
    xorAll (xs ++ ys) = xorAll xs ^^^ xorAll ys := by
  unfold xorAll
  rw [Array.foldl_append]
  have h := foldl_xor_init ys.toList (xs.foldl (fun acc x => acc ^^^ x) 0)
  simpa [Array.foldl_toList] using h

theorem xorAll_extract_succ (arr : Array Nat) (i : Nat) (hi : i < arr.size) :
    xorAll (arr.extract 0 (i + 1)) = xorAll (arr.extract 0 i) ^^^ arr[i]! := by
  have hextract : arr.extract 0 (i + 1) = arr.extract 0 i ++ #[arr[i]!] := by
    apply Array.ext
    · simp [Array.size_extract, Nat.min_eq_left (by omega : i + 1 ≤ arr.size),
        Nat.min_eq_left (by omega : i ≤ arr.size)]
    · intro j hj1 hj2
      simp [Array.size_extract, Nat.min_eq_left (by omega : i + 1 ≤ arr.size)] at hj1
      by_cases hji : j < i
      · rw [Array.getElem_append_left (by simpa [Array.size_extract, Nat.min_eq_left (by omega : i ≤ arr.size)])]
        simp [Array.getElem_extract]
      · have hj_eq : j = i := by omega
        subst j
        have hlen : (arr.extract 0 i).size = i := by
          simp [Array.size_extract, Nat.min_eq_left (by omega : i ≤ arr.size)]
        rw [Array.getElem_append_right (by rw [hlen]; omega)]
        simp [hlen, getElem!_pos arr i hi]
  rw [hextract, xorAll_append]
  simp [xorAll]

theorem subarrayXor_eq_pref_xor (arr : Array Nat) (l r : Nat)
    (hlr : l ≤ r) (hr : r < arr.size) :
    subarrayXor arr l r = xorAll (arr.extract 0 (r + 1)) ^^^ xorAll (arr.extract 0 l) := by
  unfold subarrayXor subarray
  have hsplit : arr.extract 0 (r + 1) = arr.extract 0 l ++ arr.extract l (r + 1) := by
    apply Array.ext
    · simp [Array.size_extract, Nat.min_eq_left (by omega : r + 1 ≤ arr.size)]
      omega
    · intro j hj1 hj2
      simp [Array.size_extract, Nat.min_eq_left (by omega : r + 1 ≤ arr.size)] at hj1
      have hl_sz : (arr.extract 0 l).size = l := by
        simp [Array.size_extract, Nat.min_eq_left (by omega : l ≤ arr.size)]
      by_cases hjl : j < l
      · rw [Array.getElem_append_left (by rw [hl_sz]; exact hjl)]
        simp [Array.getElem_extract]
      · rw [Array.getElem_append_right (by rw [hl_sz]; omega)]
        simp [hl_sz, Array.getElem_extract]
        congr 1
        omega
  rw [hsplit, xorAll_append]
  calc
    xorAll (arr.extract l (r + 1)) = 0 ^^^ xorAll (arr.extract l (r + 1)) := by simp [Nat.zero_xor]
    _ = (xorAll (arr.extract 0 l) ^^^ xorAll (arr.extract 0 l)) ^^^ xorAll (arr.extract l (r + 1)) := by
      simp [Nat.xor_self]
    _ = (xorAll (arr.extract 0 l) ^^^ xorAll (arr.extract l (r + 1))) ^^^ xorAll (arr.extract 0 l) := by
      simp [Nat.xor_assoc, Nat.xor_comm (xorAll (arr.extract 0 l))]

prove_correct xorQueries by
  velvet_vcgen [xorQueries, postcondition] with try finish
  case pref_correct_prefix =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simp [xorAll]
  case pref_correct_prefix =>
    rename_i arr _
    intro k hk
    by_cases hki : k ≤ i
    · have hne : k ≠ i + 1 := by omega
      rw [getElem!_set!_ne pref (i + 1) k (pref[i]! ^^^ arr[i]!) (by omega) (by omega) hne]
      exact pref_correct_prefix k hki
    · have hkeq : k = i + 1 := by omega
      subst k
      rw [getElem!_set!_eq pref (i + 1) (pref[i]! ^^^ arr[i]!) (by omega)]
      rw [pref_correct_prefix i (by omega)]
      exact (xorAll_extract_succ arr i building_pref).symm
  case ans_correct_prefix =>
    rename_i arr queries
    intro k hk
    by_cases hkj : k < j
    · have hne : k ≠ j := by omega
      rw [getElem!_set!_ne ans j k (pref[queries[j]!.2 + 1]! ^^^ pref[queries[j]!.1]!) (by omega) (by omega) hne]
      exact ans_correct_prefix k hkj
    · have hkeq : k = j := by omega
      subst k
      rw [getElem!_set!_eq ans j (pref[queries[j]!.2 + 1]! ^^^ pref[queries[j]!.1]!) (by omega)]
      have hq := valid_queries j answering
      have hl := hq.1
      have hr := hq.2
      have hpr : pref[queries[j]!.2 + 1]! = xorAll (arr.extract 0 (queries[j]!.2 + 1)) := by
        rw [pref_correct_prefix (queries[j]!.2 + 1) (by omega)]
      have hpl : pref[queries[j]!.1]! = xorAll (arr.extract 0 queries[j]!.1) := by
        rw [pref_correct_prefix queries[j]!.1 (by omega)]
      rw [hpr, hpl]
      exact (subarrayXor_eq_pref_xor arr queries[j]!.1 queries[j]!.2 hl hr).symm
  case correct_answer =>
    exact ⟨ans_size, fun k hk => ans_correct_prefix k (by omega)⟩

end Proof

end XORQueriesOfASubarray
