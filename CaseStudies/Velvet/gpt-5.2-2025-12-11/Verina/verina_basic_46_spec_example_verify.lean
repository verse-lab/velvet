import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isSortedNondecreasing (arr : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < arr.size → arr[i]! ≤ arr[j]!

def occurs (arr : Array Int) (x : Int) : Prop :=
  ∃ (i : Nat), i < arr.size ∧ arr[i]! = x

def notOccurs (arr : Array Int) (x : Int) : Prop :=
  ∀ (i : Nat), i < arr.size → arr[i]! ≠ x


def isValidIndexInt (arr : Array Int) (idx : Int) : Prop :=
  0 ≤ idx ∧ Int.toNat idx < arr.size

def idxNat (idx : Int) : Nat :=
  Int.toNat idx




def precondition (arr : Array Int) (elem : Int) : Prop :=
  isSortedNondecreasing arr

def postcondition (arr : Array Int) (elem : Int) (result : Int) : Prop :=
  (result = (-1) ∧ notOccurs arr elem) ∨
  (isValidIndexInt arr result ∧
    arr[idxNat result]! = elem ∧
    (∀ (j : Nat), idxNat result < j → j < arr.size → arr[j]! ≠ elem) ∧
    (∀ (i : Nat), i < arr.size → arr[i]! = elem → i ≤ idxNat result))


def test1_arr : Array Int := #[1, 2, 2, 3, 4, 5]

def test1_elem : Int := 2

def test1_Expected : Int := 2

def test4_arr : Array Int := #[1]

def test4_elem : Int := 1

def test4_Expected : Int := 0

def test8_arr : Array Int := #[-3, -1, -1, 0, 7]

def test8_elem : Int := -1

def test8_Expected : Int := 2







section Proof
theorem test1_precondition : precondition test1_arr test1_elem := by
  unfold precondition
  unfold isSortedNondecreasing
  intro i j hij hj
  -- `test1_arr = #[1,2,2,3,4,5]` has size 6, so `j < 6`.
  have hj' : j < 6 := by
    simpa [test1_arr] using hj
  have hi' : i < 6 := lt_trans hij hj'
  -- Now enumerate all possible `j` (since `j < 6`) and within each case all possible `i < j`.
  interval_cases j <;> interval_cases i <;> simp [test1_arr] at hij hi' hj' ⊢

theorem test1_postcondition : postcondition test1_arr test1_elem test1_Expected := by
  -- Step 1: unfold postcondition and concrete test constants; choose the second disjunct
  unfold postcondition
  right

  -- Step 4: compute idxNat and array size for this concrete instance
  have h_idxNat : idxNat (2 : Int) = 2 := by
    unfold idxNat
    simpa using (Int.toNat_ofNat 2)
  have h_size : test1_arr.size = 6 := by
    simp [test1_arr]

  -- Step 5: prove (1) isValidIndexInt test1_arr 2
  have h_valid : isValidIndexInt test1_arr (2 : Int) := by
    unfold isValidIndexInt
    constructor
    · decide
    · -- Int.toNat 2 < test1_arr.size
      simpa [h_size] using (show (2 : Nat) < 6 from by decide)

  -- Step 6: prove (2) test1_arr[idxNat 2]! = 2
  have h_at : test1_arr[idxNat (2 : Int)]! = (2 : Int) := by
    -- rewrite idxNat 2 = 2 and evaluate the literal array at index 2
    simp [h_idxNat, test1_arr]

  -- Step 7: prove (3) no later occurrences after idxNat 2 (i.e. after index 2)
  have h_noLater :
      ∀ (j : Nat), idxNat (2 : Int) < j → j < test1_arr.size → test1_arr[j]! ≠ (2 : Int) := by
    intro j hj hjsz
    have hjsz' : j < 6 := by simpa [h_size] using hjsz
    have hj' : 2 < j := by simpa [h_idxNat] using hj
    interval_cases j <;> simp [test1_arr] at hj' hjsz' ⊢

  -- Step 8: prove (4) any index containing 2 is ≤ idxNat 2 (i.e. ≤ 2)
  have h_last :
      ∀ (i : Nat), i < test1_arr.size → test1_arr[i]! = (2 : Int) → i ≤ idxNat (2 : Int) := by
    intro i hisz hiEq
    have hisz' : i < 6 := by simpa [h_size] using hisz
    interval_cases i <;> simp [test1_arr, h_idxNat] at hiEq ⊢

  -- Step 9: assemble the right-branch conjunction for postcondition
  refine And.intro h_valid ?_
  refine And.intro h_at ?_
  refine And.intro h_noLater ?_
  exact h_last

theorem test4_precondition : precondition test4_arr test4_elem := by
  unfold precondition
  unfold isSortedNondecreasing
  intro i j hij hj
  have hj' : j < 1 := by simpa [test4_arr] using hj
  have hj0 : j = 0 := (Nat.lt_one_iff.mp hj')
  have : i < 0 := by simpa [hj0] using hij
  exact (Nat.not_lt_zero i this).elim

theorem test4_postcondition : postcondition test4_arr test4_elem test4_Expected := by
  -- Step 1-2: unfold postcondition; we will prove the "found index" (right) disjunct
  unfold postcondition
  right

  -- Step 3-4: compute idxNat 0 and the array size
  have h_idxNat : idxNat (0 : Int) = 0 := by
    unfold idxNat
    simpa using (Int.toNat_ofNat 0)
  have h_size : test4_arr.size = 1 := by
    simp [test4_arr]

  -- Step 3: prove the returned index is valid
  have h_valid : isValidIndexInt test4_arr (0 : Int) := by
    unfold isValidIndexInt
    constructor
    · decide
    · -- Int.toNat 0 < test4_arr.size
      simpa [h_size] using (show (0 : Nat) < 1 from by decide)

  -- Step 4: show the array at idxNat 0 equals the searched element
  have h_at : test4_arr[idxNat (0 : Int)]! = test4_elem := by
    -- idxNat 0 = 0 and test4_arr = #[1]
    simp [h_idxNat, test4_arr, test4_elem]

  -- Step 5: show there are no later occurrences (vacuous since size = 1)
  have h_noLater :
      ∀ (j : Nat), idxNat (0 : Int) < j → j < test4_arr.size → test4_arr[j]! ≠ test4_elem := by
    intro j hj hjsz
    have hjsz' : j < 1 := by simpa [h_size] using hjsz
    have hj' : 0 < j := by simpa [h_idxNat] using hj
    have hj0 : j = 0 := (Nat.lt_one_iff.mp hjsz')
    have : ¬ (0 < j) := by simpa [hj0]
    exact (this hj').elim

  -- Step 6: show every occurrence is at an index ≤ idxNat 0
  have h_last :
      ∀ (i : Nat), i < test4_arr.size → test4_arr[i]! = test4_elem → i ≤ idxNat (0 : Int) := by
    intro i hisz hiEq
    have hisz' : i < 1 := by simpa [h_size] using hisz
    have hi0 : i = 0 := (Nat.lt_one_iff.mp hisz')
    simpa [hi0, h_idxNat]

  -- Step 7: assemble the conjunction for the right disjunct
  refine And.intro h_valid ?_
  refine And.intro h_at ?_
  refine And.intro h_noLater ?_
  exact h_last

theorem test8_precondition : precondition test8_arr test8_elem := by
  unfold precondition
  unfold isSortedNondecreasing
  intro i j hij hj
  have hj' : j < 5 := by simpa [test8_arr] using hj
  have hi' : i < 5 := Nat.lt_trans hij hj'
  interval_cases j <;> interval_cases i <;> simp [test8_arr] at hij hi' hj' ⊢

theorem test8_postcondition : postcondition test8_arr test8_elem test8_Expected := by
  -- Step 1: unfold postcondition and concrete constants; choose the second disjunct
  unfold postcondition
  right

  -- Step 3: compute idxNat for this concrete result
  have h_idxNat : idxNat (2 : Int) = 2 := by
    unfold idxNat
    simpa using (Int.toNat_ofNat 2)

  -- Step 4: compute the array size
  have h_size : test8_arr.size = 5 := by
    simp [test8_arr]

  -- Step 5: prove isValidIndexInt test8_arr 2
  have h_valid : isValidIndexInt test8_arr (2 : Int) := by
    unfold isValidIndexInt
    constructor
    · decide
    · simpa [h_size] using (show (2 : Nat) < 5 from by decide)

  -- Step 6: prove test8_arr[idxNat 2]! = test8_elem
  have h_at : test8_arr[idxNat (2 : Int)]! = test8_elem := by
    simp [h_idxNat, test8_arr, test8_elem]

  -- Step 7: prove no later occurrences after idxNat 2
  have h_noLater :
      ∀ (j : Nat), idxNat (2 : Int) < j → j < test8_arr.size → test8_arr[j]! ≠ test8_elem := by
    intro j hj hjsz
    have hjsz' : j < 5 := by simpa [h_size] using hjsz
    have hj' : 2 < j := by simpa [h_idxNat] using hj
    interval_cases j <;> simp [test8_arr, test8_elem] at hj' hjsz' ⊢

  -- Step 8: prove every occurrence is at an index ≤ idxNat 2
  have h_last :
      ∀ (i : Nat), i < test8_arr.size → test8_arr[i]! = test8_elem → i ≤ idxNat (2 : Int) := by
    intro i hisz hiEq
    have hisz' : i < 5 := by simpa [h_size] using hisz
    interval_cases i <;> simp [test8_arr, test8_elem, h_idxNat] at hiEq ⊢

  -- Step 9: assemble the right-branch conjunction
  refine And.intro h_valid ?_
  refine And.intro h_at ?_
  refine And.intro h_noLater ?_
  exact h_last

theorem uniqueness
    (arr : Array Int)
    (elem : Int)
    : precondition arr elem →
  (∀ ret1 ret2,
    postcondition arr elem ret1 →
    postcondition arr elem ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 h1 h2
  -- We only use the shape of the postcondition; precondition is irrelevant for uniqueness.
  rcases h1 with ⟨hret1, hno1⟩ | hfound1
  · -- ret1 = -1 and elem does not occur
    rcases h2 with ⟨hret2, hno2⟩ | hfound2
    · -- ret2 = -1 as well
      simpa [hret1, hret2]
    · -- ret2 is a valid index with arr[idxNat ret2] = elem, contradicting notOccurs
      rcases hfound2 with ⟨hvalid2, hat2, _hnoLater2, _hallLe2⟩
      have hidx2 : Int.toNat ret2 < arr.size := hvalid2.2
      have : arr[idxNat ret2]! ≠ elem := hno1 (idxNat ret2) hidx2
      exact (this hat2).elim
  · -- ret1 is found
    rcases hfound1 with ⟨hvalid1, hat1, _hnoLater1, hallLe1⟩
    rcases h2 with ⟨hret2, hno2⟩ | hfound2
    · -- ret2 = -1 and elem does not occur, contradicting that ret1 points to elem
      have hidx1 : Int.toNat ret1 < arr.size := hvalid1.2
      have : arr[idxNat ret1]! ≠ elem := hno2 (idxNat ret1) hidx1
      exact (this hat1).elim
    · -- both are found; show indices equal, then results equal by Int.toNat injectivity on nonneg ints
      rcases hfound2 with ⟨hvalid2, hat2, _hnoLater2, hallLe2⟩
      have hidx1 : Int.toNat ret1 < arr.size := hvalid1.2
      have hidx2 : Int.toNat ret2 < arr.size := hvalid2.2
      have hle21 : idxNat ret2 ≤ idxNat ret1 := hallLe1 (idxNat ret2) hidx2 hat2
      have hle12 : idxNat ret1 ≤ idxNat ret2 := hallLe2 (idxNat ret1) hidx1 hat1
      have hEqNat : idxNat ret1 = idxNat ret2 := Nat.le_antisymm hle12 hle21
      -- convert Nat equality to Int equality using nonnegativity
      have hnonneg1 : 0 ≤ ret1 := hvalid1.1
      have hnonneg2 : 0 ≤ ret2 := hvalid2.1
      -- (ret.toNat : Int) = ret for nonnegative ret
      have htn1 : (Int.toNat ret1 : Int) = ret1 := Int.toNat_of_nonneg hnonneg1
      have htn2 : (Int.toNat ret2 : Int) = ret2 := Int.toNat_of_nonneg hnonneg2
      -- cast the Nat equality to Int and rewrite
      have hEqIntNat : (Int.toNat ret1 : Int) = (Int.toNat ret2 : Int) := by
        exact congrArg (fun n : Nat => (n : Int)) hEqNat
      -- finish
      calc
        ret1 = (Int.toNat ret1 : Int) := by simpa [htn1] using (Eq.symm htn1)
        _ = (Int.toNat ret2 : Int) := by simpa using hEqIntNat
        _ = ret2 := by simpa [htn2] using htn2
end Proof
