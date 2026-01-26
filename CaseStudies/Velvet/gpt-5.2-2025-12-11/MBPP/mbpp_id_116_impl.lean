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
    mbpp_id_116: convert a given sequence of positive integers into a single integer.
    Natural language breakdown:
    1. The input is a finite sequence of integers intended to represent base-10 digits.
    2. Each element must be a single decimal digit, i.e., it lies between 0 and 9 inclusive.
    3. The output integer is obtained by concatenating these digits in order.
    4. For input length n, the result equals the positional-value sum:
       res = Σ (i = 0..n-1), digit(i) * 10^(n-1-i).
    5. If the sequence is empty, the concatenation represents 0.

    Note on wording:
    - The prompt says "positive integers", but the intended behavior from examples is
      digit concatenation in base 10, which naturally allows digit 0 (e.g., leading zeros).
      We therefore model the domain as decimal digits 0..9.
-/

section Specs
-- Helper: all elements are valid base-10 digits.
-- We use Array Int to match the Velvet method signature.
def digitsOk (s1 : Array Int) : Prop :=
  ∀ (i : Nat), i < s1.size → (0 ≤ s1[i]!) ∧ (s1[i]! ≤ 9)

-- Helper: positional-value characterization using a finite sum over indices.
-- We avoid big-operator notation (∑ i in ...) to prevent parser issues.
def digitsValue (s1 : Array Int) : Int :=
  (Finset.range s1.size).sum (fun (i : Nat) =>
    s1[i]! * (10 : Int) ^ (s1.size - 1 - i))

-- Preconditions: all entries are digits.
def precondition (s1 : Array Int) : Prop :=
  digitsOk s1

-- Postcondition: result equals the base-10 positional-value sum.
def postcondition (s1 : Array Int) (res : Int) : Prop :=
  res = digitsValue s1
end Specs

section Impl
method sequenceToInt (s1: Array Int) return (res: Int)
  require precondition s1
  ensures postcondition s1 res
  do
  let mut acc : Int := 0
  let mut i : Nat := 0
  while i < s1.size
    -- Invariant: loop index stays within bounds.
    -- Init: i = 0. Preserved: i increases by 1 while guard ensures i < size.
    invariant "idx_bounds" i ≤ s1.size
    -- Invariant: accumulator equals the value of the prefix of length i.
    -- Init: i=0, acc=0 matches empty prefix sum. Preserved by acc := acc*10 + digit.
    -- Exit: i = s1.size gives acc = digitsValue s1.
    invariant "acc_prefix_value"
      acc = (Finset.range i).sum (fun (j : Nat) =>
        s1[j]! * (10 : Int) ^ (i - 1 - j))
  do
    acc := acc * 10 + s1[i]!
    i := i + 1
  return acc
end Impl

section TestCases
-- Test case 1: example [1,2,3] -> 123
-- (Must include problem example as test case 1)
def test1_s1 : Array Int := #[1, 2, 3]
def test1_Expected : Int := 123

-- Test case 2: example [4,5,6] -> 456
def test2_s1 : Array Int := #[4, 5, 6]
def test2_Expected : Int := 456

-- Test case 3: example [5,6,7] -> 567
def test3_s1 : Array Int := #[5, 6, 7]
def test3_Expected : Int := 567

-- Test case 4: single digit
def test4_s1 : Array Int := #[9]
def test4_Expected : Int := 9

-- Test case 5: empty sequence -> 0
def test5_s1 : Array Int := #[]
def test5_Expected : Int := 0

-- Test case 6: leading zeros do not change the numeric value
def test6_s1 : Array Int := #[0, 0, 7]
def test6_Expected : Int := 7

-- Test case 7: internal zeros
def test7_s1 : Array Int := #[1, 0, 2, 0]
def test7_Expected : Int := 1020

-- Test case 8: typical longer input
def test8_s1 : Array Int := #[8, 3, 1, 4, 2]
def test8_Expected : Int := 83142

-- Test case 9: all zeros
def test9_s1 : Array Int := #[0, 0, 0, 0]
def test9_Expected : Int := 0

-- IMPORTANT: All expected outputs MUST use format testN_Expected (capital E)
-- Recommend to validate: test1, test5, test7
end TestCases

section Assertions
-- Test case 1

#assert_same_evaluation #[((sequenceToInt test1_s1).run), DivM.res test1_Expected ]

-- Test case 2

#assert_same_evaluation #[((sequenceToInt test2_s1).run), DivM.res test2_Expected ]

-- Test case 3

#assert_same_evaluation #[((sequenceToInt test3_s1).run), DivM.res test3_Expected ]

-- Test case 4

#assert_same_evaluation #[((sequenceToInt test4_s1).run), DivM.res test4_Expected ]

-- Test case 5

#assert_same_evaluation #[((sequenceToInt test5_s1).run), DivM.res test5_Expected ]

-- Test case 6

#assert_same_evaluation #[((sequenceToInt test6_s1).run), DivM.res test6_Expected ]

-- Test case 7

#assert_same_evaluation #[((sequenceToInt test7_s1).run), DivM.res test7_Expected ]

-- Test case 8

#assert_same_evaluation #[((sequenceToInt test8_s1).run), DivM.res test8_Expected ]

-- Test case 9

#assert_same_evaluation #[((sequenceToInt test9_s1).run), DivM.res test9_Expected ]
end Assertions

section Pbt
extract_program_for sequenceToInt
prove_precondition_decidable_for sequenceToInt
prove_postcondition_decidable_for sequenceToInt
derive_tester_for sequenceToInt
run_elab do
  let g : Plausible.Gen (_ × Bool) := do
    let arg_0 ← Plausible.SampleableExt.interpSample (Array Int)
    let res := sequenceToIntTester arg_0
    pure ((arg_0), res)
  for _ in [1: 200] do
    let res ← Plausible.Gen.run g 20
    unless res.2 do
      IO.println s!"Postcondition violated for input {res.1}"
      break
    
end Pbt

section Proof
set_option maxHeartbeats 10000000


-- prove_correct sequenceToInt by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0_0
    (s1 : Array ℤ)
    (acc : ℤ)
    (i : ℕ)
    : ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x) * 10 = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - x) := by
    classical
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxlt : x < i := by
      simpa [Finset.mem_range] using hx
    have hpos : 1 ≤ i - x := Nat.sub_pos_of_lt hxlt
    have hsub : i - x = (i - 1 - x) + 1 := by
      -- i - x = (i - x - 1) + 1, and i - x - 1 = i - 1 - x
      calc
        i - x = (i - x - 1) + 1 := (Nat.sub_add_cancel hpos).symm
        _ = (i - 1 - x) + 1 := by
          -- (i - x - 1) = (i - 1 - x)
          -- rewrite as i - x - 1 = i - (x+1) and i - 1 - x = i - (1+x)
          simp [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    have hp : (10 : ℤ) ^ (i - x) = (10 : ℤ) ^ (i - 1 - x) * (10 : ℤ) := by
      calc
        (10 : ℤ) ^ (i - x) = (10 : ℤ) ^ ((i - 1 - x) + 1) := by
          simpa [hsub]
        _ = (10 : ℤ) ^ (i - 1 - x) * (10 : ℤ) := by
          simpa using (pow_succ (10 : ℤ) (i - 1 - x))
    calc
      s1[x]! * (10 : ℤ) ^ (i - 1 - x) * 10
          = s1[x]! * ((10 : ℤ) ^ (i - 1 - x) * (10 : ℤ)) := by
              simp [Int.mul_assoc]
      _   = s1[x]! * (10 : ℤ) ^ (i - x) := by
              -- rewrite the parenthesized power-product as 10^(i-x)
              simpa [hp, Int.mul_assoc]


theorem goal_0_1
    (s1 : Array ℤ)
    (acc : ℤ)
    (i : ℕ)
    (invariant_acc_prefix_value : acc = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x))
    (if_pos : i < s1.size)
    (h_mul_sum_right : (∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x)) * 10 = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x) * 10)
    (h_term_shift : ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x) * 10 = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - x))
    (h_acc_mul10 : acc = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x))
    : acc * 10 = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - x) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_0_2
    (s1 : Array ℤ)
    (acc : ℤ)
    (i : ℕ)
    (invariant_acc_prefix_value : acc = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x))
    (if_pos : i < s1.size)
    (h_acc_mul10 : acc * 10 = (∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x)) * 10)
    (h_mul_sum_right : (∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x)) * 10 = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x) * 10)
    (h_term_shift : ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x) * 10 = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - x))
    (h_acc_mul10_as_sum : acc * 10 = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - x))
    : s1[i]! = s1[i]! * 10 ^ (i - i) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )


theorem goal_0_3
    (s1 : Array ℤ)
    (acc : ℤ)
    (i : ℕ)
    : ∑ x ∈ Finset.range (i + 1), s1[x]! * 10 ^ (i - x) = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - x) + s1[i]! := by
  -- standard range-splitting at the last index
  simpa [Nat.sub_self, pow_zero, mul_one, add_comm, add_left_comm, add_assoc] using
    (Finset.sum_range_succ (fun x : ℕ => s1[x]! * (10 : ℤ) ^ (i - x)) i)

theorem goal_0
    (s1 : Array ℤ)
    (acc : ℤ)
    (i : ℕ)
    (invariant_acc_prefix_value : acc = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x))
    (if_pos : i < s1.size)
    : acc * 10 + s1[i]! = ∑ x ∈ Finset.range (i + 1), s1[x]! * 10 ^ (i - x) := by
    -- Step 3: shift the invariant sum by multiplying by 10
    have h_acc_mul10 : acc * 10 = (∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x)) * 10 := by
      -- from invariant_acc_prefix_value
      (try simp at *; expose_names); exact invariant_acc_prefix_value; done
    have h_mul_sum_right : (∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x)) * 10 =
        ∑ x ∈ Finset.range i, (s1[x]! * 10 ^ (i - 1 - x)) * 10 := by
      -- push (*10) inside the sum
      (try simp at *; expose_names); exact (Finset.sum_mul (Finset.range i) (fun i_1 ↦ s1[i_1]! * 10 ^ (i - 1 - i_1)) 10); done
    have h_term_shift : (∑ x ∈ Finset.range i, (s1[x]! * 10 ^ (i - 1 - x)) * 10) =
        ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - x) := by
      -- use Int.pow_succ / Int.pow_succ' and arithmetic on exponents: (i - 1 - x) + 1 = i - x
      (try simp at *; expose_names); exact (goal_0_0 s1 acc i); done
    have h_acc_mul10_as_sum : acc * 10 = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - x) := by
      -- combine previous three
      (try simp at *; expose_names); exact (goal_0_1 s1 acc i invariant_acc_prefix_value if_pos h_mul_sum_right h_term_shift h_acc_mul10); done

    -- Step 4: rewrite the new digit as the last term (x = i) of the new-range sum
    have h_last_term : s1[i]! = s1[i]! * 10 ^ (i - i) := by
      -- simp [Nat.sub_self]
      (try simp at *; expose_names); exact (goal_0_2 s1 acc i invariant_acc_prefix_value if_pos h_acc_mul10 h_mul_sum_right h_term_shift h_acc_mul10_as_sum); done

    -- Step 5: split the target sum over range (i+1) into range i plus last term
    have h_sum_split :
        (∑ x ∈ Finset.range (i + 1), s1[x]! * 10 ^ (i - x)) =
          (∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - x)) + (s1[i]! * 10 ^ (i - i)) := by
      -- Finset.sum_range_succ with f x := s1[x]! * 10^(i-x)
      (try simp at *; expose_names); exact (goal_0_3 s1 acc i); done

    -- Step 6: combine everything
    calc
      acc * 10 + s1[i]!
          = (∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - x)) + s1[i]! := by
              -- rewrite acc*10 using h_acc_mul10_as_sum
              (try simp at *; expose_names); exact h_acc_mul10_as_sum; done
      _   = (∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - x)) + (s1[i]! * 10 ^ (i - i)) := by
              -- rewrite s1[i]! using h_last_term
              (try simp at *; expose_names); exact (congrArg (HAdd.hAdd (∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - x))) h_last_term); done
      _   = ∑ x ∈ Finset.range (i + 1), s1[x]! * 10 ^ (i - x) := by
              -- rewrite using h_sum_split (symm)
              (try simp at *; expose_names); exact id (Eq.symm h_sum_split); done

theorem goal_1
    (s1 : Array ℤ)
    : 0 = ∑ x ∈ Finset.range 0, s1[x]! * 10 ^ (0 - 1 - x) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2
    (s1 : Array ℤ)
    (acc : ℤ)
    (i : ℕ)
    (invariant_idx_bounds : i ≤ s1.size)
    (invariant_acc_prefix_value : acc = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x))
    (i_1 : ℤ)
    (i_2 : ℕ)
    (done_1 : s1.size ≤ i)
    (i_3 : acc = i_1 ∧ i = i_2)
    : postcondition s1 i_1 := by
  have hi : i = s1.size := Nat.le_antisymm invariant_idx_bounds done_1
  have hacc : i_1 = acc := by
    exact (Eq.symm i_3.1)
  -- rewrite the invariant at termination
  have haccValue : acc = digitsValue s1 := by
    -- substitute i = s1.size in the invariant
    simpa [digitsValue, hi] using invariant_acc_prefix_value
  -- finish: postcondition is res = digitsValue s1
  unfold postcondition
  calc
    i_1 = acc := hacc
    _ = digitsValue s1 := haccValue


theorem goal_0'
    (s1 : Array ℤ)
    (acc : ℤ)
    (i : ℕ)
    (invariant_acc_prefix_value : acc = ∑ x ∈ Finset.range i, s1[x]! * 10 ^ (i - 1 - x))
    (if_pos : i < s1.size)
    : acc * 10 + s1[i]! = ∑ x ∈ Finset.range (i + 1), s1[x]! * 10 ^ (i - x) := by

    subst_vars
    plausible (config := { numInst := 10000 })

prove_correct sequenceToInt by
  loom_solve <;> (try simp at *; expose_names)
  {  }
  -- exact (goal_0 s1 acc i invariant_acc_prefix_value if_pos)
  -- exact (goal_1 s1)
  -- exact (goal_2 s1 acc i invariant_idx_bounds invariant_acc_prefix_value i_1 i_2 done_1 i_3)
end Proof
