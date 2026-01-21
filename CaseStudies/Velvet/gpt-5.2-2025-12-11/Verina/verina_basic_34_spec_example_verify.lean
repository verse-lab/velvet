import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def isEvenInt (x : Int) : Bool :=
  decide (x % 2 = 0)

def precondition (arr : Array Int) : Prop :=
  True

def postcondition (arr : Array Int) (result : Array Int) : Prop :=
  let l := arr.toList
  let r := result.toList

  r.Sublist l ∧

  (∀ x, x ∈ r → isEvenInt x = true) ∧

  (∀ x,
      (isEvenInt x = true → r.count x = l.count x) ∧
      (isEvenInt x = false → r.count x = 0))


def test1_arr : Array Int := #[1, 2, 3, 4, 5, 6]

def test1_Expected : Array Int := #[2, 4, 6]

def test5_arr : Array Int := #[0, -2, -3, -4, 5]

def test5_Expected : Array Int := #[0, -2, -4]

def test6_arr : Array Int := #[2, 2, 3, 2, 4, 4, 5]

def test6_Expected : Array Int := #[2, 2, 2, 4, 4]







section Proof
theorem test1_precondition :
  precondition test1_arr := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition_0
    (l : List ℤ := test1_arr.toList)
    (hl : l = [1, 2, 3, 4, 5, 6])
    (hl_def : l = test1_arr.toList)
    (r : List ℤ := test1_Expected.toList)
    (hr : r = [2, 4, 6])
    (hr_def : r = test1_Expected.toList)
    (hl' : l = [1, 2, 3, 4, 5, 6])
    (hr' : r = [2, 4, 6])
    (hSub : r.Sublist l)
    (x : ℤ)
    (hx : x ∈ r)
    : isEvenInt x = true := by
  have hx' : x ∈ ([2, 4, 6] : List ℤ) := by
    simpa [hr] using hx
  have hxCases : x = 2 ∨ x = 4 ∨ x = 6 := by
    simpa using hx'
  rcases hxCases with h2 | hrest
  · subst h2
    unfold isEvenInt
    native_decide
  · rcases hrest with h4 | h6
    · subst h4
      unfold isEvenInt
      native_decide
    · subst h6
      unfold isEvenInt
      native_decide

theorem test1_postcondition_1
    (l : List ℤ := test1_arr.toList)
    (hl : l = [1, 2, 3, 4, 5, 6])
    (hl_def : l = test1_arr.toList)
    (r : List ℤ := test1_Expected.toList)
    (hr : r = [2, 4, 6])
    (hr_def : r = test1_Expected.toList)
    (hl' : l = [1, 2, 3, 4, 5, 6])
    (hr' : r = [2, 4, 6])
    (hSub : r.Sublist l)
    (hAllEven : ∀ x ∈ r, isEvenInt x = true)
    (x : ℤ)
    (hxEven : isEvenInt x = true)
    : List.count x r = List.count x l := by
    -- This test instance is not generally true: e.g. x = 0 is even,
    -- but count 0 r = 0 while count 0 l = 0 (ok), however x = 8 is even,
    -- still both counts are 0 (ok). The problematic case is x = 0 is fine.
    -- Actually the real issue is that the statement cannot be derived from
    -- the given hypotheses alone (it would require the stronger postcondition
    -- clause relating counts). We can exhibit a counterexample by taking x = 0?
    -- That doesn't refute. Take x = 2: works. The statement happens to be true
    -- for these concrete lists for all x, so we prove it by case split on mem.
    subst hl'
    subst hr'
    by_cases hx2 : x = 2
    · subst hx2; decide
    by_cases hx4 : x = 4
    · subst hx4; decide
    by_cases hx6 : x = 6
    · subst hx6; decide
    -- Otherwise x is not 2,4,6 so it's not in r, and also not in l (since l has only 1..6)
    have hxr : x ∉ ([2, 4, 6] : List ℤ) := by
      simp [List.mem_cons, hx2, hx4, hx6]
    have hxl : x ∉ ([1, 2, 3, 4, 5, 6] : List ℤ) := by
      -- reduce membership to disjunctions and discharge using the negated equalities
      have hx1 : x ≠ 1 := by
        intro h; subst h
        -- 1 is not even, contradict hxEven
        dsimp [isEvenInt] at hxEven
        -- decide (1 % 2 = 0) is false
        simpa using hxEven
      have hx3 : x ≠ 3 := by
        intro h; subst h
        dsimp [isEvenInt] at hxEven
        simpa using hxEven
      have hx5 : x ≠ 5 := by
        intro h; subst h
        dsimp [isEvenInt] at hxEven
        simpa using hxEven
      simp [List.mem_cons, hx1, hx2, hx3, hx4, hx5, hx6]
    simp [List.count_eq_zero_of_not_mem, hxr, hxl]

theorem test1_postcondition_2
    (l : List ℤ := test1_arr.toList)
    (hl : l = [1, 2, 3, 4, 5, 6])
    (hl_def : l = test1_arr.toList)
    (r : List ℤ := test1_Expected.toList)
    (hr : r = [2, 4, 6])
    (hr_def : r = test1_Expected.toList)
    (hl' : l = [1, 2, 3, 4, 5, 6])
    (hr' : r = [2, 4, 6])
    (hSub : r.Sublist l)
    (hAllEven : ∀ x ∈ r, isEvenInt x = true)
    (x : ℤ)
    (hxNotEven : isEvenInt x = false)
    : List.count x r = 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition :
  postcondition test1_arr test1_Expected := by
  -- Step 1: unfold the concrete goal and introduce the local names `l` and `r`
  dsimp [postcondition]
  -- Goal is now a conjunction about `l := test1_arr.toList` and `r := test1_Expected.toList`.

  -- Step 2: compute the concrete lists
  have hl : test1_arr.toList = [1, 2, 3, 4, 5, 6] := by
    (try simp at *; expose_names); exact rfl; done
  have hr : test1_Expected.toList = [2, 4, 6] := by
    (try simp at *; expose_names); exact rfl; done

  -- We will use `l` and `r` as abbreviations for readability.
  set l : List Int := test1_arr.toList with hl_def
  set r : List Int := test1_Expected.toList with hr_def

  -- Rewrite `l` and `r` to the concrete lists computed above.
  have hl' : l = [1, 2, 3, 4, 5, 6] := by
    -- from `hl_def` and `hl`
    (try simp at *; expose_names); exact hl; done
  have hr' : r = [2, 4, 6] := by
    -- from `hr_def` and `hr`
    (try simp at *; expose_names); exact hr; done

  -- Step 3: prove the sublist requirement `r.Sublist l`
  have hSub : r.Sublist l := by
    -- use `hl'` and `hr'` and build a `List.Sublist` proof by constructors (skip 1, keep 2, skip 3, keep 4, skip 5, keep 6)
    (try simp at *; expose_names); exact List.isSublist_iff_sublist.mp rfl; done

  -- Step 4: prove every element of `r` is even
  have hAllEven : ∀ x, x ∈ r → isEvenInt x = true := by
    intro x hx
    -- reduce membership in `[2,4,6]` to cases, then compute `isEvenInt` on numerals
    -- using `hr'` to rewrite `r`
    (try simp at *; expose_names); exact (test1_postcondition_0 l hl hl_def r hr hr_def hl' hr' hSub x hx); done

  -- Step 5: prove the counting/multiplicity conditions
  have hCount :
      ∀ x,
        (isEvenInt x = true → r.count x = l.count x) ∧
        (isEvenInt x = false → r.count x = 0) := by
    intro x
    constructor

    · -- Step 6: even case -> counts match
      intro hxEven
      -- split into cases based on whether x is 2, 4, 6, or something else (still even)
      -- use `hl'` and `hr'` to compute `count` on explicit lists via `List.count_cons` / simp
      (try simp at *; expose_names); exact (test1_postcondition_1 l hl hl_def r hr hr_def hl' hr' hSub hAllEven x hxEven); done

    · -- Step 7: odd/non-even case -> count in r is zero
      intro hxNotEven
      -- since all elements of r are even (hAllEven), x cannot be in r; then use `List.count_eq_zero_of_not_mem`
      -- to conclude `r.count x = 0`
      (try simp at *; expose_names); exact (test1_postcondition_2 l hl hl_def r hr hr_def hl' hr' hSub hAllEven x hxNotEven); done

  -- Step 8: combine all parts into the conjunction required by `postcondition`
  refine And.intro ?_ (And.intro ?_ ?_)
  · exact hSub
  · exact hAllEven
  · exact hCount

theorem test5_precondition :
  precondition test5_arr := by
  intros; expose_names; exact (trivial); done

theorem test5_postcondition_0
    (l : List ℤ := test5_arr.toList)
    (hl : l = [0, -2, -3, -4, 5])
    (hl_def : l = test5_arr.toList)
    (r : List ℤ := test5_Expected.toList)
    (hr : r = [0, -2, -4])
    (hr_def : r = test5_Expected.toList)
    (hl' : l = [0, -2, -3, -4, 5])
    (hr' : r = [0, -2, -4])
    (hSub : r.Sublist l)
    : ∀ x ∈ r, isEvenInt x = true := by
    intro x hx
    -- reduce membership using the concrete list for `r`
    have hx' : x ∈ ([0, -2, -4] : List ℤ) := by simpa [hr'] using hx
    -- split cases from membership in the explicit list
    rcases (by simpa using hx' : x = 0 ∨ x = -2 ∨ x = -4) with h0 | h2 | h4
    · subst h0
      unfold isEvenInt
      native_decide
    · subst h2
      unfold isEvenInt
      native_decide
    · subst h4
      unfold isEvenInt
      native_decide

theorem test5_postcondition_1
    (l : List ℤ := test5_arr.toList)
    (hl : l = [0, -2, -3, -4, 5])
    (hl_def : l = test5_arr.toList)
    (r : List ℤ := test5_Expected.toList)
    (hr : r = [0, -2, -4])
    (hr_def : r = test5_Expected.toList)
    (hl' : l = [0, -2, -3, -4, 5])
    (hr' : r = [0, -2, -4])
    (hSub : r.Sublist l)
    (hAllEven : ∀ x ∈ r, isEvenInt x = true)
    (x : ℤ)
    (hxEven : isEvenInt x = true)
    : x = 0 ∨ x = -2 ∨ x = -4 ∨ ¬x = 0 ∧ ¬x = -2 ∧ ¬x = -4 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test5_postcondition_3
    (l : List ℤ := test5_arr.toList)
    (hl : l = [0, -2, -3, -4, 5])
    (hl_def : l = test5_arr.toList)
    (r : List ℤ := test5_Expected.toList)
    (hr : r = [0, -2, -4])
    (hr_def : r = test5_Expected.toList)
    (hl' : l = [0, -2, -3, -4, 5])
    (hr' : r = [0, -2, -4])
    (hSub : r.Sublist l)
    (hAllEven : ∀ x ∈ r, isEvenInt x = true)
    (x : ℤ)
    (hxNotEven : isEvenInt x = false)
    : x ∉ r := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test5_postcondition_2
    (l : List ℤ := test5_arr.toList)
    (hl : l = [0, -2, -3, -4, 5])
    (hl_def : l = test5_arr.toList)
    (r : List ℤ := test5_Expected.toList)
    (hr : r = [0, -2, -4])
    (hr_def : r = test5_Expected.toList)
    (hl' : l = [0, -2, -3, -4, 5])
    (hr' : r = [0, -2, -4])
    (hSub : r.Sublist l)
    (hAllEven : ∀ x ∈ r, isEvenInt x = true)
    (x : ℤ)
    (hxEven : isEvenInt x = true)
    (hCases : x = 0 ∨ x = -2 ∨ x = -4 ∨ ¬x = 0 ∧ ¬x = -2 ∧ ¬x = -4)
    : List.count x r = List.count x l := by
    sorry

theorem test5_postcondition :
  postcondition test5_arr test5_Expected := by
  -- Step 1: unfold the concrete goal and introduce local names `l` and `r`
  dsimp [postcondition]

  -- Step 2: compute the concrete lists for this test
  have hl : test5_arr.toList = [0, -2, -3, -4, 5] := by (try simp at *; expose_names); exact rfl; done
  have hr : test5_Expected.toList = [0, -2, -4] := by (try simp at *; expose_names); exact rfl; done

  -- Abbreviate for readability (as in test1 proof)
  set l : List Int := test5_arr.toList with hl_def
  set r : List Int := test5_Expected.toList with hr_def

  -- Rewrite `l` and `r` to the concrete lists computed above
  have hl' : l = [0, -2, -3, -4, 5] := by (try simp at *; expose_names); exact hl; done
  have hr' : r = [0, -2, -4] := by (try simp at *; expose_names); exact hr; done

  -- Step 3: prove the sublist requirement `r.Sublist l`
  have hSub : r.Sublist l := by (try simp at *; expose_names); exact (List.isSublist_iff_sublist.mp rfl); done

  -- Step 4: prove every element of `r` is even
  have hAllEven : ∀ x, x ∈ r → isEvenInt x = true := by (try simp at *; expose_names); exact (test5_postcondition_0 l hl hl_def r hr hr_def hl' hr' hSub); done

  -- Step 5: prove the counting/multiplicity conditions (split into even/odd implications)
  have hCount :
      ∀ x,
        (isEvenInt x = true → r.count x = l.count x) ∧
        (isEvenInt x = false → r.count x = 0) := by
    intro x
    constructor
    · -- Step 6: even case -> counts match (case split on x = 0, -2, -4, otherwise not in either list)
      intro hxEven
      have hCases : x = 0 ∨ x = (-2) ∨ x = (-4) ∨ (x ≠ 0 ∧ x ≠ (-2) ∧ x ≠ (-4)) := by (try simp at *; expose_names); exact (test5_postcondition_1 l hl hl_def r hr hr_def hl' hr' hSub hAllEven x hxEven); done
      have hCountEq : r.count x = l.count x := by (try simp at *; expose_names); exact (test5_postcondition_2 l hl hl_def r hr hr_def hl' hr' hSub hAllEven x hxEven hCases); done
      exact hCountEq
    · -- Step 7: odd/non-even case -> count in r is zero (use all-even to show x ∉ r, then count_eq_zero_of_not_mem)
      intro hxNotEven
      have hxNotMem : x ∉ r := by (try simp at *; expose_names); exact (test5_postcondition_3 l hl hl_def r hr hr_def hl' hr' hSub hAllEven x hxNotEven); done
      have hCountZero : r.count x = 0 := by (try simp at *; expose_names); exact (List.count_eq_zero.mpr hxNotMem); done
      exact hCountZero

  -- Step 8: combine all parts into the conjunction required by `postcondition`
  refine And.intro ?_ (And.intro ?_ ?_)
  · exact hSub
  · exact hAllEven
  · exact hCount
end Proof
