import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL
import CaseStudies.Velvet.Utils
import CaseStudies.Velvet.UtilsLemmas
import Mathlib.Tactic
-- Never add new imports here

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    Compare: Determine whether two integer values are equal
    Natural language breakdown:
    1. We are given two integers a and b.
    2. The result is a Boolean indicating whether the two integers are equal.
    3. If a equals b, the function returns true.
    4. If a does not equal b, the function returns false.
    5. There are no invalid inputs and no preconditions on a or b.
    6. The output must be uniquely determined by equality of a and b.
-/

section Specs
-- No helper definitions are needed: equality on Int is decidable in Lean/Mathlib.

def precondition (a : Int) (b : Int) : Prop :=
  True

-- Specify both Boolean cases to make the spec proof-friendly and fully characterizing.
-- Together, these two equivalences uniquely determine `result`.

def postcondition (a : Int) (b : Int) (result : Bool) : Prop :=
  (result = true ↔ a = b) ∧ (result = false ↔ a ≠ b)
end Specs

section Impl
method Compare (a : Int) (b : Int)
  return (result : Bool)
  require precondition a b
  ensures postcondition a b result
  do
    if a = b then
      return true
    else
      return false
end Impl

section TestCases
-- Test case 1: example from prompt, equal positives
-- Most important example

def test1_a : Int := 1

def test1_b : Int := 1

def test1_Expected : Bool := true

-- Test case 2: example from prompt, different positives
-- Most important example

def test2_a : Int := 1

def test2_b : Int := 2

def test2_Expected : Bool := false

-- Test case 3: equal negatives
-- Most important example

def test3_a : Int := (-5)

def test3_b : Int := (-5)

def test3_Expected : Bool := true

-- Test case 4: different negatives

def test4_a : Int := (-5)

def test4_b : Int := (-6)

def test4_Expected : Bool := false

-- Test case 5: zero equals zero

def test5_a : Int := 0

def test5_b : Int := 0

def test5_Expected : Bool := true

-- Test case 6: negative vs zero

def test6_a : Int := (-1)

def test6_b : Int := 0

def test6_Expected : Bool := false

-- Test case 7: positive vs negative with same magnitude

def test7_a : Int := 7

def test7_b : Int := (-7)

def test7_Expected : Bool := false

-- Test case 8: larger equal values

def test8_a : Int := 123456

def test8_b : Int := 123456

def test8_Expected : Bool := true

-- Test case 9: larger different values

def test9_a : Int := 123456

def test9_b : Int := 123457

def test9_Expected : Bool := false

-- Recommend to validate: test1, test2, test3
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((Compare test1_a test1_b).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((Compare test2_a test2_b).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((Compare test3_a test3_b).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((Compare test4_a test4_b).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((Compare test5_a test5_b).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((Compare test6_a test6_b).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((Compare test7_a test7_b).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((Compare test8_a test8_b).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((Compare test9_a test9_b).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for Compare
prove_precondition_decidable_for Compare
prove_postcondition_decidable_for Compare
derive_tester_for Compare
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Int)
    let arg_1 ← Plausible.SampleableExt.interpSample (Int)
    let res := CompareTester arg_0 arg_1
    pure ((arg_0, arg_1), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct Compare by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0
    (a : ℤ)
    (b : ℤ)
    (if_pos : a = b)
    : postcondition a b true := by
    unfold postcondition
    constructor
    · constructor
      · intro _
        exact if_pos
      · intro _
        rfl
    · constructor
      · intro h
        cases h
      · intro hne
        exfalso
        exact hne if_pos

theorem goal_1
    (a : ℤ)
    (b : ℤ)
    (if_neg : ¬a = b)
    : postcondition a b false := by
    unfold postcondition
    constructor
    · constructor
      · intro h
        exfalso
        exact Bool.false_ne_true h
      · intro hab
        exfalso
        exact Bool.false_ne_true (False.elim (if_neg hab))
    · constructor
      · intro h
        simpa using if_neg
      · intro hne
        rfl


prove_correct Compare by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 a b if_pos)
  exact (goal_1 a b if_neg)
end Proof
