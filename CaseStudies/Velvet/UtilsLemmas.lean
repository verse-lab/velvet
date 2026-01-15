/-
Velvet Utils Lemmas
===================

Lemmas about the utility functions defined in Utils.lean.
Extracted from various example files in VelvetExamples/.

Contents:
- Lemmas about array multiset operations
- Lemmas about array element swapping
-/

import CaseStudies.Velvet.Utils

/-! ## Multiset Lemmas -/

section ArrayMultiset

/-- If two multisets are equal, their list representations have the same length -/
@[simp, grind]
lemma sameCardMultisetImpliesSameLengthLists {m1 m2: Multiset Int} :
    (h: m1 = m2) -> m1.toList.length = m2.toList.length := by
  intro h
  subst h
  simp_all only [Multiset.length_toList]

/-- If two arrays have the same multiset representation, they have the same size -/
@[simp, grind]
lemma multiSetSameImpliesSameSize {arr1 arr2: Array Int} :
    (h: arrayToMultiset arr1 = arrayToMultiset arr2) -> arr1.size = arr2.size := by
  unfold arrayToMultiset
  intro h
  apply sameCardMultisetImpliesSameLengthLists at h
  simp[*] at h
  grind

end ArrayMultiset

/-! ## Array Swapping Lemmas -/

section ArraySwap

/-- Swapping preserves array size -/
@[simp, grind]
lemma elemSwap!_size {arr: Array Int} {l r: Nat} :
    (elemSwap! arr l r).size = arr.size := by
  simp [elemSwap!]

/-- After swapping, the left index contains the right's original value -/
@[simp, grind]
lemma elemSwap!_left {arr: Array Int} {l r: Nat} {hl : l < arr.size} {hr: r < arr.size} :
    (elemSwap! arr l r)[l]! = arr[r]! := by
  simp [elemSwap!]
  unfold Array.setIfInBounds
  split_ifs with h <;> simp[*]
  · simp [Array.getElem_set]
    intro hlr
    aesop

/-- After swapping, the right index contains the left's original value -/
@[simp, grind]
lemma elemSwap!_right {arr: Array Int} {l r: Nat} {hl : l < arr.size} {hr: r < arr.size} :
    (elemSwap! arr l r)[r]! = arr[l]! := by
  simp [elemSwap!]
  unfold Array.setIfInBounds
  split_ifs with h <;> simp[*]
  · simp [Array.getElem_set]
    aesop

/-- Swapping doesn't affect indices different from both swap positions -/
@[simp, grind]
lemma elemSwap!_different {arr: Array Int} {l r: Nat} {k: Nat}
    {hl : l < arr.size} {hr: r < arr.size}
    {hkl : ¬ k = l} {hkr : ¬ k = r} {hk : k < arr.size} :
    (elemSwap! arr l r)[k]! = arr[k]! := by
  simp [elemSwap!]
  unfold Array.setIfInBounds
  split_ifs with h <;> (simp[*] ; grind)

/-- Conditional element access after swap -/
@[simp, grind]
lemma elemSwap!_different' {arr: Array Int} {l r: Nat} {k: Nat}
    {hl : l < arr.size} {hr: r < arr.size} :
    (elemSwap! arr l r)[k]! =
      if l = k then arr[r]!
      else if r = k then arr[l]!
      else arr[k]! := by
  split_ifs with hif
  · grind
  · grind
  · grind

/-- Swapping two elements preserves the multiset representation of an array -/
@[simp, grind]
lemma multiSet_swap! {arr: Array Int} {idx₁ idx₂ : Nat}
    {h_idx₁: idx₁ < arr.size} {h_idx₂: idx₂ < arr.size} :
    arrayToMultiset (elemSwap! arr idx₁ idx₂) = arrayToMultiset arr := by
  classical
  unfold elemSwap!
  unfold arrayToMultiset
  simp [List.perm_iff_count]
  intro a
  rw [List.count_set] <;> try simp [*]
  rw [List.count_set] <;> try simp [*]
  simp [List.getElem_set]
  split_ifs with h <;> try simp
  have : Array.count a arr > 0 := by
    apply Array.count_pos_iff.mpr; simp [<-h]
  omega

end ArraySwap
