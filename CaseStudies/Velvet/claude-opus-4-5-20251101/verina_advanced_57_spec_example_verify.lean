import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def allUnique (l : List Int) : Prop :=
  l.Nodup

def isSubsetOf (l1 : List Int) (l2 : List Int) : Prop :=
  ∀ x, x ∈ l1 → x ∈ l2



def require1 (nums1 : List Int) (_nums2 : List Int) :=
  allUnique nums1

def require2 (_nums1 : List Int) (nums2 : List Int) :=
  allUnique nums2

def require3 (nums1 : List Int) (nums2 : List Int) :=
  isSubsetOf nums1 nums2


def ensures1 (nums1 : List Int) (_nums2 : List Int) (result : List Int) :=
  result.length = nums1.length





def ensures2 (nums1 : List Int) (nums2 : List Int) (result : List Int) :=
  ∀ i : Nat, i < nums1.length →
    let x := nums1[i]!
    let xPos := nums2.findIdx (· == x)

    (result[i]! = -1 ∧ 
     ∀ j : Nat, xPos < j → j < nums2.length → nums2[j]! ≤ x) ∨

    (result[i]! ≠ -1 ∧ 
     ∃ k : Nat, xPos < k ∧ k < nums2.length ∧ 
          nums2[k]! = result[i]! ∧ 
          result[i]! > x ∧
          ∀ j : Nat, xPos < j → j < k → nums2[j]! ≤ x)

def precondition (nums1 : List Int) (nums2 : List Int) :=
  require1 nums1 nums2 ∧ require2 nums1 nums2 ∧ require3 nums1 nums2

def postcondition (nums1 : List Int) (nums2 : List Int) (result : List Int) :=
  ensures1 nums1 nums2 result ∧ ensures2 nums1 nums2 result


def test1_nums1 : List Int := [4, 1, 2]

def test1_nums2 : List Int := [1, 3, 4, 2]

def test1_Expected : List Int := [-1, 3, -1]

def test2_nums1 : List Int := [2, 4]

def test2_nums2 : List Int := [1, 2, 3, 4]

def test2_Expected : List Int := [3, -1]

def test6_nums1 : List Int := [1, 2, 3]

def test6_nums2 : List Int := [3, 2, 1, 4]

def test6_Expected : List Int := [4, 4, 4]







section Proof
theorem test1_precondition :
  precondition test1_nums1 test1_nums2 := by
  unfold precondition require1 require2 require3 allUnique isSubsetOf
  unfold test1_nums1 test1_nums2
  constructor
  · -- Nodup [4, 1, 2]
    simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self]
    decide
  constructor
  · -- Nodup [1, 3, 4, 2]
    simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self]
    decide
  · -- isSubsetOf [4, 1, 2] [1, 3, 4, 2]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · -- x = 4: need 4 ∈ [1, 3, 4, 2], i.e., 4 = 1 ∨ 4 = 3 ∨ 4 = 4 ∨ 4 = 2
      right; right; left; rfl
    · -- x = 1: need 1 ∈ [1, 3, 4, 2], i.e., 1 = 1 ∨ ...
      left; rfl
    · -- x = 2: need 2 ∈ [1, 3, 4, 2], i.e., 2 = 1 ∨ 2 = 3 ∨ 2 = 4 ∨ 2 = 2
      right; right; right; rfl

theorem test1_postcondition_0
    (h_ensures1 : ensures1 test1_nums1 test1_nums2 test1_Expected)
    : (test1_Expected[0]?.getD 0 = -1 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[0]?.getD 0) test1_nums2 < j → j < test1_nums2.length → test1_nums2[j]?.getD 0 ≤ test1_nums1[0]?.getD 0) ∨ ¬test1_Expected[0]?.getD 0 = -1 ∧ ∃ k, List.findIdx (fun x ↦ x == test1_nums1[0]?.getD 0) test1_nums2 < k ∧ k < test1_nums2.length ∧ test1_nums2[k]?.getD 0 = test1_Expected[0]?.getD 0 ∧ test1_nums1[0]?.getD 0 < test1_Expected[0]?.getD 0 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[0]?.getD 0) test1_nums2 < j → j < k → test1_nums2[j]?.getD 0 ≤ test1_nums1[0]?.getD 0 := by
    left
    constructor
    · native_decide
    · intro j hfind hlen
      have h1 : List.findIdx (fun x ↦ x == test1_nums1[0]?.getD 0) test1_nums2 = 2 := by native_decide
      have h2 : test1_nums2.length = 4 := by native_decide
      rw [h1] at hfind
      rw [h2] at hlen
      have hj : j = 3 := by omega
      subst hj
      native_decide

theorem test1_postcondition_1
    (h_ensures1 : ensures1 test1_nums1 test1_nums2 test1_Expected)
    (h_i0 : (test1_Expected[0]?.getD 0 = -1 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[0]?.getD 0) test1_nums2 < j → j < test1_nums2.length → test1_nums2[j]?.getD 0 ≤ test1_nums1[0]?.getD 0) ∨ ¬test1_Expected[0]?.getD 0 = -1 ∧ ∃ k, List.findIdx (fun x ↦ x == test1_nums1[0]?.getD 0) test1_nums2 < k ∧ k < test1_nums2.length ∧ test1_nums2[k]?.getD 0 = test1_Expected[0]?.getD 0 ∧ test1_nums1[0]?.getD 0 < test1_Expected[0]?.getD 0 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[0]?.getD 0) test1_nums2 < j → j < k → test1_nums2[j]?.getD 0 ≤ test1_nums1[0]?.getD 0)
    : (test1_Expected[1]?.getD 0 = -1 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[1]?.getD 0) test1_nums2 < j → j < test1_nums2.length → test1_nums2[j]?.getD 0 ≤ test1_nums1[1]?.getD 0) ∨ ¬test1_Expected[1]?.getD 0 = -1 ∧ ∃ k, List.findIdx (fun x ↦ x == test1_nums1[1]?.getD 0) test1_nums2 < k ∧ k < test1_nums2.length ∧ test1_nums2[k]?.getD 0 = test1_Expected[1]?.getD 0 ∧ test1_nums1[1]?.getD 0 < test1_Expected[1]?.getD 0 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[1]?.getD 0) test1_nums2 < j → j < k → test1_nums2[j]?.getD 0 ≤ test1_nums1[1]?.getD 0 := by
    right
    constructor
    · native_decide
    · use 1
      constructor
      · native_decide
      · constructor
        · native_decide
        · constructor
          · native_decide
          · constructor
            · native_decide
            · intro j hj1 hj2
              omega

theorem test1_postcondition_2
    (h_ensures1 : ensures1 test1_nums1 test1_nums2 test1_Expected)
    (h_i0 : (test1_Expected[0]?.getD 0 = -1 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[0]?.getD 0) test1_nums2 < j → j < test1_nums2.length → test1_nums2[j]?.getD 0 ≤ test1_nums1[0]?.getD 0) ∨ ¬test1_Expected[0]?.getD 0 = -1 ∧ ∃ k, List.findIdx (fun x ↦ x == test1_nums1[0]?.getD 0) test1_nums2 < k ∧ k < test1_nums2.length ∧ test1_nums2[k]?.getD 0 = test1_Expected[0]?.getD 0 ∧ test1_nums1[0]?.getD 0 < test1_Expected[0]?.getD 0 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[0]?.getD 0) test1_nums2 < j → j < k → test1_nums2[j]?.getD 0 ≤ test1_nums1[0]?.getD 0)
    (h_i1 : (test1_Expected[1]?.getD 0 = -1 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[1]?.getD 0) test1_nums2 < j → j < test1_nums2.length → test1_nums2[j]?.getD 0 ≤ test1_nums1[1]?.getD 0) ∨ ¬test1_Expected[1]?.getD 0 = -1 ∧ ∃ k, List.findIdx (fun x ↦ x == test1_nums1[1]?.getD 0) test1_nums2 < k ∧ k < test1_nums2.length ∧ test1_nums2[k]?.getD 0 = test1_Expected[1]?.getD 0 ∧ test1_nums1[1]?.getD 0 < test1_Expected[1]?.getD 0 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[1]?.getD 0) test1_nums2 < j → j < k → test1_nums2[j]?.getD 0 ≤ test1_nums1[1]?.getD 0)
    : (test1_Expected[2]?.getD 0 = -1 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[2]?.getD 0) test1_nums2 < j → j < test1_nums2.length → test1_nums2[j]?.getD 0 ≤ test1_nums1[2]?.getD 0) ∨ ¬test1_Expected[2]?.getD 0 = -1 ∧ ∃ k, List.findIdx (fun x ↦ x == test1_nums1[2]?.getD 0) test1_nums2 < k ∧ k < test1_nums2.length ∧ test1_nums2[k]?.getD 0 = test1_Expected[2]?.getD 0 ∧ test1_nums1[2]?.getD 0 < test1_Expected[2]?.getD 0 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[2]?.getD 0) test1_nums2 < j → j < k → test1_nums2[j]?.getD 0 ≤ test1_nums1[2]?.getD 0 := by
    left
    constructor
    · native_decide
    · intro j hj1 hj2
      have h_findIdx : List.findIdx (fun x ↦ x == test1_nums1[2]?.getD 0) test1_nums2 = 3 := by native_decide
      have h_len : test1_nums2.length = 4 := by native_decide
      rw [h_findIdx] at hj1
      rw [h_len] at hj2
      omega

theorem test1_postcondition_3
    (h_ensures1 : ensures1 test1_nums1 test1_nums2 test1_Expected)
    (h_i0 : (test1_Expected[0]?.getD 0 = -1 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[0]?.getD 0) test1_nums2 < j → j < test1_nums2.length → test1_nums2[j]?.getD 0 ≤ test1_nums1[0]?.getD 0) ∨ ¬test1_Expected[0]?.getD 0 = -1 ∧ ∃ k, List.findIdx (fun x ↦ x == test1_nums1[0]?.getD 0) test1_nums2 < k ∧ k < test1_nums2.length ∧ test1_nums2[k]?.getD 0 = test1_Expected[0]?.getD 0 ∧ test1_nums1[0]?.getD 0 < test1_Expected[0]?.getD 0 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[0]?.getD 0) test1_nums2 < j → j < k → test1_nums2[j]?.getD 0 ≤ test1_nums1[0]?.getD 0)
    (h_i1 : (test1_Expected[1]?.getD 0 = -1 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[1]?.getD 0) test1_nums2 < j → j < test1_nums2.length → test1_nums2[j]?.getD 0 ≤ test1_nums1[1]?.getD 0) ∨ ¬test1_Expected[1]?.getD 0 = -1 ∧ ∃ k, List.findIdx (fun x ↦ x == test1_nums1[1]?.getD 0) test1_nums2 < k ∧ k < test1_nums2.length ∧ test1_nums2[k]?.getD 0 = test1_Expected[1]?.getD 0 ∧ test1_nums1[1]?.getD 0 < test1_Expected[1]?.getD 0 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[1]?.getD 0) test1_nums2 < j → j < k → test1_nums2[j]?.getD 0 ≤ test1_nums1[1]?.getD 0)
    (h_i2 : (test1_Expected[2]?.getD 0 = -1 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[2]?.getD 0) test1_nums2 < j → j < test1_nums2.length → test1_nums2[j]?.getD 0 ≤ test1_nums1[2]?.getD 0) ∨ ¬test1_Expected[2]?.getD 0 = -1 ∧ ∃ k, List.findIdx (fun x ↦ x == test1_nums1[2]?.getD 0) test1_nums2 < k ∧ k < test1_nums2.length ∧ test1_nums2[k]?.getD 0 = test1_Expected[2]?.getD 0 ∧ test1_nums1[2]?.getD 0 < test1_Expected[2]?.getD 0 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test1_nums1[2]?.getD 0) test1_nums2 < j → j < k → test1_nums2[j]?.getD 0 ≤ test1_nums1[2]?.getD 0)
    : ensures2 test1_nums1 test1_nums2 test1_Expected := by
    unfold ensures2
    intro i hi
    have hlen : test1_nums1.length = 3 := by native_decide
    rw [hlen] at hi
    match i with
    | 0 =>
      simp only [test1_nums1, test1_nums2, test1_Expected, List.getElem!_eq_getElem?_getD]
      convert h_i0 using 2 <;> native_decide
    | 1 =>
      simp only [test1_nums1, test1_nums2, test1_Expected, List.getElem!_eq_getElem?_getD]
      convert h_i1 using 2 <;> native_decide
    | 2 =>
      simp only [test1_nums1, test1_nums2, test1_Expected, List.getElem!_eq_getElem?_getD]
      convert h_i2 using 2 <;> native_decide
    | n + 3 => omega

theorem test1_postcondition :
  postcondition test1_nums1 test1_nums2 test1_Expected := by
  -- First, establish that ensures1 holds (length equality)
  have h_ensures1 : ensures1 test1_nums1 test1_nums2 test1_Expected := by
    (try simp at *; expose_names); exact rfl; done
  -- Second, establish ensures2 for index 0 (x=4 at position 2 in nums2, result=-1)
  have h_i0 : let x := test1_nums1[0]!; let xPos := test1_nums2.findIdx (· == x); 
    (test1_Expected[0]! = -1 ∧ ∀ j : Nat, xPos < j → j < test1_nums2.length → test1_nums2[j]! ≤ x) ∨
    (test1_Expected[0]! ≠ -1 ∧ ∃ k : Nat, xPos < k ∧ k < test1_nums2.length ∧ test1_nums2[k]! = test1_Expected[0]! ∧ test1_Expected[0]! > x ∧ ∀ j : Nat, xPos < j → j < k → test1_nums2[j]! ≤ x) := by
    (try simp at *; expose_names); exact (test1_postcondition_0 h_ensures1); done
  -- Third, establish ensures2 for index 1 (x=1 at position 0 in nums2, result=3)
  have h_i1 : let x := test1_nums1[1]!; let xPos := test1_nums2.findIdx (· == x);
    (test1_Expected[1]! = -1 ∧ ∀ j : Nat, xPos < j → j < test1_nums2.length → test1_nums2[j]! ≤ x) ∨
    (test1_Expected[1]! ≠ -1 ∧ ∃ k : Nat, xPos < k ∧ k < test1_nums2.length ∧ test1_nums2[k]! = test1_Expected[1]! ∧ test1_Expected[1]! > x ∧ ∀ j : Nat, xPos < j → j < k → test1_nums2[j]! ≤ x) := by
    (try simp at *; expose_names); exact (test1_postcondition_1 h_ensures1 h_i0); done
  -- Fourth, establish ensures2 for index 2 (x=2 at position 3 in nums2, result=-1)
  have h_i2 : let x := test1_nums1[2]!; let xPos := test1_nums2.findIdx (· == x);
    (test1_Expected[2]! = -1 ∧ ∀ j : Nat, xPos < j → j < test1_nums2.length → test1_nums2[j]! ≤ x) ∨
    (test1_Expected[2]! ≠ -1 ∧ ∃ k : Nat, xPos < k ∧ k < test1_nums2.length ∧ test1_nums2[k]! = test1_Expected[2]! ∧ test1_Expected[2]! > x ∧ ∀ j : Nat, xPos < j → j < k → test1_nums2[j]! ≤ x) := by
    (try simp at *; expose_names); exact (test1_postcondition_2 h_ensures1 h_i0 h_i1); done
  -- Now combine to get ensures2
  have h_ensures2 : ensures2 test1_nums1 test1_nums2 test1_Expected := by
    (try simp at *; expose_names); exact (test1_postcondition_3 h_ensures1 h_i0 h_i1 h_i2); done
  -- Finally combine ensures1 and ensures2 into postcondition
  unfold postcondition
  exact ⟨h_ensures1, h_ensures2⟩

theorem test2_precondition :
  precondition test2_nums1 test2_nums2 := by
  unfold precondition require1 require2 require3 allUnique isSubsetOf
  unfold test2_nums1 test2_nums2
  constructor
  · -- require1: [2, 4].Nodup
    decide
  constructor
  · -- require2: [1, 2, 3, 4].Nodup
    decide
  · -- require3: isSubsetOf [2, 4] [1, 2, 3, 4]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    cases hx with
    | inl h => simp [h]
    | inr h => simp [h]

theorem test2_postcondition_0
    (h_ensures1 : ensures1 test2_nums1 test2_nums2 test2_Expected)
    : (test2_Expected[0]?.getD 0 = -1 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test2_nums1[0]?.getD 0) test2_nums2 < j → j < test2_nums2.length → test2_nums2[j]?.getD 0 ≤ test2_nums1[0]?.getD 0) ∨ ¬test2_Expected[0]?.getD 0 = -1 ∧ ∃ k, List.findIdx (fun x ↦ x == test2_nums1[0]?.getD 0) test2_nums2 < k ∧ k < test2_nums2.length ∧ test2_nums2[k]?.getD 0 = test2_Expected[0]?.getD 0 ∧ test2_nums1[0]?.getD 0 < test2_Expected[0]?.getD 0 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test2_nums1[0]?.getD 0) test2_nums2 < j → j < k → test2_nums2[j]?.getD 0 ≤ test2_nums1[0]?.getD 0 := by
    right
    constructor
    · native_decide
    · use 2
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · native_decide
      · native_decide
      · native_decide
      · native_decide
      · intro j hj1 hj2
        have h1 : List.findIdx (fun x ↦ x == test2_nums1[0]?.getD 0) test2_nums2 = 1 := by native_decide
        rw [h1] at hj1
        omega

theorem test2_postcondition_1
    (h_ensures1 : ensures1 test2_nums1 test2_nums2 test2_Expected)
    (h_i0 : (test2_Expected[0]?.getD 0 = -1 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test2_nums1[0]?.getD 0) test2_nums2 < j → j < test2_nums2.length → test2_nums2[j]?.getD 0 ≤ test2_nums1[0]?.getD 0) ∨ ¬test2_Expected[0]?.getD 0 = -1 ∧ ∃ k, List.findIdx (fun x ↦ x == test2_nums1[0]?.getD 0) test2_nums2 < k ∧ k < test2_nums2.length ∧ test2_nums2[k]?.getD 0 = test2_Expected[0]?.getD 0 ∧ test2_nums1[0]?.getD 0 < test2_Expected[0]?.getD 0 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test2_nums1[0]?.getD 0) test2_nums2 < j → j < k → test2_nums2[j]?.getD 0 ≤ test2_nums1[0]?.getD 0)
    : (test2_Expected[1]?.getD 0 = -1 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test2_nums1[1]?.getD 0) test2_nums2 < j → j < test2_nums2.length → test2_nums2[j]?.getD 0 ≤ test2_nums1[1]?.getD 0) ∨ ¬test2_Expected[1]?.getD 0 = -1 ∧ ∃ k, List.findIdx (fun x ↦ x == test2_nums1[1]?.getD 0) test2_nums2 < k ∧ k < test2_nums2.length ∧ test2_nums2[k]?.getD 0 = test2_Expected[1]?.getD 0 ∧ test2_nums1[1]?.getD 0 < test2_Expected[1]?.getD 0 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test2_nums1[1]?.getD 0) test2_nums2 < j → j < k → test2_nums2[j]?.getD 0 ≤ test2_nums1[1]?.getD 0 := by
    left
    constructor
    · native_decide
    · intro j hfind hlen
      have h1 : List.findIdx (fun x ↦ x == test2_nums1[1]?.getD 0) test2_nums2 = 3 := by native_decide
      have h2 : test2_nums2.length = 4 := by native_decide
      rw [h1] at hfind
      rw [h2] at hlen
      omega

theorem test2_postcondition_2
    (h_ensures1 : ensures1 test2_nums1 test2_nums2 test2_Expected)
    (h_i0 : (test2_Expected[0]?.getD 0 = -1 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test2_nums1[0]?.getD 0) test2_nums2 < j → j < test2_nums2.length → test2_nums2[j]?.getD 0 ≤ test2_nums1[0]?.getD 0) ∨ ¬test2_Expected[0]?.getD 0 = -1 ∧ ∃ k, List.findIdx (fun x ↦ x == test2_nums1[0]?.getD 0) test2_nums2 < k ∧ k < test2_nums2.length ∧ test2_nums2[k]?.getD 0 = test2_Expected[0]?.getD 0 ∧ test2_nums1[0]?.getD 0 < test2_Expected[0]?.getD 0 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test2_nums1[0]?.getD 0) test2_nums2 < j → j < k → test2_nums2[j]?.getD 0 ≤ test2_nums1[0]?.getD 0)
    (h_i1 : (test2_Expected[1]?.getD 0 = -1 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test2_nums1[1]?.getD 0) test2_nums2 < j → j < test2_nums2.length → test2_nums2[j]?.getD 0 ≤ test2_nums1[1]?.getD 0) ∨ ¬test2_Expected[1]?.getD 0 = -1 ∧ ∃ k, List.findIdx (fun x ↦ x == test2_nums1[1]?.getD 0) test2_nums2 < k ∧ k < test2_nums2.length ∧ test2_nums2[k]?.getD 0 = test2_Expected[1]?.getD 0 ∧ test2_nums1[1]?.getD 0 < test2_Expected[1]?.getD 0 ∧ ∀ (j : ℕ), List.findIdx (fun x ↦ x == test2_nums1[1]?.getD 0) test2_nums2 < j → j < k → test2_nums2[j]?.getD 0 ≤ test2_nums1[1]?.getD 0)
    : ensures2 test2_nums1 test2_nums2 test2_Expected := by
    sorry

theorem test2_postcondition :
  postcondition test2_nums1 test2_nums2 test2_Expected := by
  -- First, establish that ensures1 holds (length equality: [3, -1].length = [2, 4].length = 2)
  have h_ensures1 : ensures1 test2_nums1 test2_nums2 test2_Expected := by
    (try simp at *; expose_names); exact rfl; done
  -- For index 0: x=2 at position 1 in nums2, result=3, need to show next greater element is 3 at position 2
  have h_i0 : let x := test2_nums1[0]!; let xPos := test2_nums2.findIdx (· == x);
    (test2_Expected[0]! = -1 ∧ ∀ j : Nat, xPos < j → j < test2_nums2.length → test2_nums2[j]! ≤ x) ∨
    (test2_Expected[0]! ≠ -1 ∧ ∃ k : Nat, xPos < k ∧ k < test2_nums2.length ∧ test2_nums2[k]! = test2_Expected[0]! ∧ test2_Expected[0]! > x ∧ ∀ j : Nat, xPos < j → j < k → test2_nums2[j]! ≤ x) := by
    (try simp at *; expose_names); exact (test2_postcondition_0 h_ensures1); done
  -- For index 1: x=4 at position 3 in nums2, result=-1, no greater element after position 3
  have h_i1 : let x := test2_nums1[1]!; let xPos := test2_nums2.findIdx (· == x);
    (test2_Expected[1]! = -1 ∧ ∀ j : Nat, xPos < j → j < test2_nums2.length → test2_nums2[j]! ≤ x) ∨
    (test2_Expected[1]! ≠ -1 ∧ ∃ k : Nat, xPos < k ∧ k < test2_nums2.length ∧ test2_nums2[k]! = test2_Expected[1]! ∧ test2_Expected[1]! > x ∧ ∀ j : Nat, xPos < j → j < k → test2_nums2[j]! ≤ x) := by
    (try simp at *; expose_names); exact (test2_postcondition_1 h_ensures1 h_i0); done
  -- Combine the index cases into ensures2
  have h_ensures2 : ensures2 test2_nums1 test2_nums2 test2_Expected := by
    (try simp at *; expose_names); exact (test2_postcondition_2 h_ensures1 h_i0 h_i1); done
  -- Finally combine ensures1 and ensures2 into postcondition
  unfold postcondition
  exact ⟨h_ensures1, h_ensures2⟩
end Proof
