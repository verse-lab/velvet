import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

method test1 (a: Nat) return (res: Nat)
  require a > 0
  ensures res > 0
  do
    let mut x := 0
    let mut t := a
    while t > 0
      invariant x + t = a
      done_with (x = 10 ∨ t = 0)
    do
      x := x + 1
      t := t - 1
      if (x = 10) then break
    return x

prove_correct test1 by loom_solve

method test2 (a: Nat) return (res: Nat)
  require a > 0
  ensures res > 0
  do
    let mut x := 0
    let mut t := a
    let mut cnt := 0
    while t > 0
      invariant x + t = a
      done_with (t = 0)
    do
      cnt := cnt + 1
      if (cnt % 2 = 0) then continue
      x := x + 1
      t := t - 1
    return x

prove_correct test2 by loom_solve

method sum_even (arr: Array Nat) return (res: Nat)
  ensures res = Array.sum (Array.filter (fun x => x % 2 = 0) arr)
  do
    let mut i := 0
    let mut s := 0
    while (i < arr.size)
      invariant i <= arr.size
      invariant s = Array.sum (Array.filter (fun x => x % 2 = 0) (Array.extract arr 0 i))
      done_with (s = Array.sum (Array.filter (fun x => x % 2 = 0) arr))
    do
      if (arr[i]! % 2 != 0) then
        i := i + 1
        continue
      s := s + arr[i]!
      i := i + 1
    return s

lemma filter_sum_snoc (arr: Array Nat) (p: Nat → Bool) :
  forall i, i < arr.size →
      (Array.filter p (Array.extract arr 0 i)).sum + (if (p arr[i]!) then arr[i]! else 0)=
      (Array.filter p (Array.extract arr 0 (i + 1))).sum := by
  intro i hi
  have extract_app : Array.extract arr 0 (i + 1) = Array.extract arr 0 i ++ #[arr[i]!] :=
    by aesop
  rw [extract_app]
  rw [Array.filter_append]
  · simp
    aesop
  · rw [Array.size_append]

attribute [grind] filter_sum_snoc

prove_correct sum_even by
  loom_solve
  rw [invariant_2]
  have i_eq_size : i = arr.size := by omega
  have extract_eq : arr = (arr.extract 0 i) := by aesop
  rw [← extract_eq]
