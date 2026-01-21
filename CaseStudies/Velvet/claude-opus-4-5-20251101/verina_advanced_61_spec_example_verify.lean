import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def listProduct (lst : List Int) : Int :=
  lst.foldl (· * ·) 1



def precondition (nums : List Int) :=
  True





def postcondition (nums : List Int) (result : List Int) :=
  result.length = nums.length ∧
  ∀ i : Nat, i < nums.length → 
    result[i]! = listProduct (nums.take i) * listProduct (nums.drop (i + 1))


def test1_nums : List Int := [1, 2, 3, 4]

def test1_Expected : List Int := [24, 12, 8, 6]

def test2_nums : List Int := [-1, 1, 0, -3, 3]

def test2_Expected : List Int := [0, 0, 9, 0, 0]

def test3_nums : List Int := [2, 3]

def test3_Expected : List Int := [3, 2]







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  unfold postcondition test1_nums test1_Expected listProduct
  constructor
  · native_decide
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | 3 => native_decide
    | n + 4 => omega

theorem test2_precondition :
  precondition test2_nums := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_nums test2_Expected := by
  unfold postcondition test2_nums test2_Expected listProduct
  constructor
  · native_decide
  · intro i hi
    simp only [List.length] at hi
    interval_cases i <;> native_decide

theorem test3_precondition :
  precondition test3_nums := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_nums test3_Expected := by
  unfold postcondition test3_nums test3_Expected
  constructor
  · native_decide
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | n + 2 => omega

theorem uniqueness_0
    (nums : List ℤ)
    (hpre : precondition nums)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (h1 : postcondition nums ret1)
    (h2 : postcondition nums ret2)
    : ret1.length = nums.length := by
    unfold postcondition at h1
    exact h1.left

theorem uniqueness_1
    (nums : List ℤ)
    (hpre : precondition nums)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (h1 : postcondition nums ret1)
    (h2 : postcondition nums ret2)
    (len1 : ret1.length = nums.length)
    : ret2.length = nums.length := by
    intros; expose_names; exact (uniqueness_0 nums hpre ret2 ret1 h2 h1); done

theorem uniqueness_2
    (nums : List ℤ)
    (hpre : precondition nums)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (h1 : postcondition nums ret1)
    (h2 : postcondition nums ret2)
    (len1 : ret1.length = nums.length)
    (len2 : ret2.length = nums.length)
    : ret1.length = ret2.length := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_3
    (nums : List ℤ)
    (hpre : precondition nums)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (h1 : postcondition nums ret1)
    (h2 : postcondition nums ret2)
    (len1 : ret1.length = nums.length)
    (len2 : ret2.length = nums.length)
    (len_eq : ret1.length = ret2.length)
    : ∀ i < nums.length, ret1[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums) := by
    intro i hi
    -- From h1, we get the postcondition property
    have h1_right := h1.2 i hi
    -- h1_right : ret1[i]! = listProduct (nums.take i) * listProduct (nums.drop (i + 1))
    -- We need to show ret1[i]?.getD 0 = listProduct (nums.take i) * listProduct (nums.drop (i + 1))
    -- First, we know i < ret1.length from len1 and hi
    have hi_ret1 : i < ret1.length := by omega
    -- Use List.getD_getElem? to simplify ret1[i]?.getD 0
    rw [List.getD_getElem?]
    simp only [hi_ret1, ↓reduceDIte]
    -- Now we have ret1[i] on the left
    -- We need to connect ret1[i]! with ret1[i]
    -- ret1[i]! when i < ret1.length equals ret1[i]
    have h_eq : ret1[i]! = ret1[i] := by
      simp only [List.getElem!_eq_getElem?_getD]
      rw [List.getD_getElem?]
      simp only [hi_ret1, ↓reduceDIte]
    rw [← h_eq]
    exact h1_right

theorem uniqueness_4
    (nums : List ℤ)
    (hpre : precondition nums)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (h1 : postcondition nums ret1)
    (h2 : postcondition nums ret2)
    (len1 : ret1.length = nums.length)
    (len2 : ret2.length = nums.length)
    (len_eq : ret1.length = ret2.length)
    (elem1 : ∀ i < nums.length, ret1[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    : ∀ i < nums.length, ret2[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums) := by
    intros; expose_names; exact (uniqueness_3 nums hpre ret2 ret1 h2 h1 len2 len1 (id (Eq.symm len_eq)) i h); done

theorem uniqueness_5
    (nums : List ℤ)
    (hpre : precondition nums)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (h1 : postcondition nums ret1)
    (h2 : postcondition nums ret2)
    (len1 : ret1.length = nums.length)
    (len2 : ret2.length = nums.length)
    (len_eq : ret1.length = ret2.length)
    (i : ℕ)
    (hi1 : i < ret1.length)
    (hi2 : i < ret2.length)
    (hi_nums : i < nums.length)
    (elem1 : ∀ i < nums.length, ret1[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (elem2 : ∀ i < nums.length, ret2[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (ret1_eq : ret1[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (ret2_eq : ret2[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    : ret1[i] = ret1[i]?.getD 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_6
    (nums : List ℤ)
    (hpre : precondition nums)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (h1 : postcondition nums ret1)
    (h2 : postcondition nums ret2)
    (len1 : ret1.length = nums.length)
    (len2 : ret2.length = nums.length)
    (len_eq : ret1.length = ret2.length)
    (i : ℕ)
    (hi1 : i < ret1.length)
    (hi2 : i < ret2.length)
    (hi_nums : i < nums.length)
    (elem1 : ∀ i < nums.length, ret1[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (elem2 : ∀ i < nums.length, ret2[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (ret1_eq : ret1[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (ret2_eq : ret2[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (ret1_getelem : ret1[i] = ret1[i]?.getD 0)
    : ret2[i] = ret2[i]?.getD 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_7
    (nums : List ℤ)
    (hpre : precondition nums)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (h1 : postcondition nums ret1)
    (h2 : postcondition nums ret2)
    (len1 : ret1.length = nums.length)
    (len2 : ret2.length = nums.length)
    (len_eq : ret1.length = ret2.length)
    (i : ℕ)
    (hi1 : i < ret1.length)
    (hi2 : i < ret2.length)
    (hi_nums : i < nums.length)
    (elem1 : ∀ i < nums.length, ret1[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (elem2 : ∀ i < nums.length, ret2[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (ret1_eq : ret1[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (ret2_eq : ret2[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (ret1_getelem : ret1[i] = ret1[i]?.getD 0)
    (ret2_getelem : ret2[i] = ret2[i]?.getD 0)
    : ret1[i] = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_8
    (nums : List ℤ)
    (hpre : precondition nums)
    (ret1 : List ℤ)
    (ret2 : List ℤ)
    (h1 : postcondition nums ret1)
    (h2 : postcondition nums ret2)
    (len1 : ret1.length = nums.length)
    (len2 : ret2.length = nums.length)
    (len_eq : ret1.length = ret2.length)
    (i : ℕ)
    (hi1 : i < ret1.length)
    (hi2 : i < ret2.length)
    (hi_nums : i < nums.length)
    (ret1_val : ret1[i] = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (elem1 : ∀ i < nums.length, ret1[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (elem2 : ∀ i < nums.length, ret2[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (ret1_eq : ret1[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (ret2_eq : ret2[i]?.getD 0 = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums))
    (ret1_getelem : ret1[i] = ret1[i]?.getD 0)
    (ret2_getelem : ret2[i] = ret2[i]?.getD 0)
    : ret2[i] = listProduct (List.take i nums) * listProduct (List.drop (i + 1) nums) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness (nums : List Int):
  precondition nums →
  (∀ ret1 ret2,
    postcondition nums ret1 →
    postcondition nums ret2 →
    ret1 = ret2) := by
  intro hpre
  intro ret1 ret2 h1 h2
  -- Extract the two parts of each postcondition
  have len1 : ret1.length = nums.length := by (try simp at *; expose_names); exact (uniqueness_0 nums hpre ret1 ret2 h1 h2); done
  have len2 : ret2.length = nums.length := by (try simp at *; expose_names); exact (uniqueness_1 nums hpre ret1 ret2 h1 h2 len1); done
  -- Show ret1 and ret2 have the same length
  have len_eq : ret1.length = ret2.length := by (try simp at *; expose_names); exact (uniqueness_2 nums hpre ret1 ret2 h1 h2 len1 len2); done
  -- Extract the element conditions from postconditions
  have elem1 : ∀ i : Nat, i < nums.length → ret1[i]! = listProduct (nums.take i) * listProduct (nums.drop (i + 1)) := by (try simp at *; expose_names); exact (uniqueness_3 nums hpre ret1 ret2 h1 h2 len1 len2 len_eq); done
  have elem2 : ∀ i : Nat, i < nums.length → ret2[i]! = listProduct (nums.take i) * listProduct (nums.drop (i + 1)) := by (try simp at *; expose_names); exact (uniqueness_4 nums hpre ret1 ret2 h1 h2 len1 len2 len_eq elem1); done
  -- Use List.ext_getElem to prove equality
  apply List.ext_getElem len_eq
  intro i hi1 hi2
  -- For each index, both elements equal the same expression
  have hi_nums : i < nums.length := by (try simp at *; expose_names); exact (Nat.lt_of_lt_of_eq hi1 len1); done
  have ret1_eq : ret1[i]! = listProduct (nums.take i) * listProduct (nums.drop (i + 1)) := by (try simp at *; expose_names); exact (elem1 i hi_nums); done
  have ret2_eq : ret2[i]! = listProduct (nums.take i) * listProduct (nums.drop (i + 1)) := by (try simp at *; expose_names); exact (elem2 i hi_nums); done
  -- Convert getElem! to getElem for valid indices
  have ret1_getelem : ret1[i] = ret1[i]! := by (try simp at *; expose_names); exact (uniqueness_5 nums hpre ret1 ret2 h1 h2 len1 len2 len_eq i hi1 hi2 hi_nums elem1 elem2 ret1_eq ret2_eq); done
  have ret2_getelem : ret2[i] = ret2[i]! := by (try simp at *; expose_names); exact (uniqueness_6 nums hpre ret1 ret2 h1 h2 len1 len2 len_eq i hi1 hi2 hi_nums elem1 elem2 ret1_eq ret2_eq ret1_getelem); done
  -- Conclude by transitivity
  have ret1_val : ret1[i] = listProduct (nums.take i) * listProduct (nums.drop (i + 1)) := by (try simp at *; expose_names); exact (uniqueness_7 nums hpre ret1 ret2 h1 h2 len1 len2 len_eq i hi1 hi2 hi_nums elem1 elem2 ret1_eq ret2_eq ret1_getelem ret2_getelem); done
  have ret2_val : ret2[i] = listProduct (nums.take i) * listProduct (nums.drop (i + 1)) := by (try simp at *; expose_names); exact (uniqueness_8 nums hpre ret1 ret2 h1 h2 len1 len2 len_eq i hi1 hi2 hi_nums ret1_val elem1 elem2 ret1_eq ret2_eq ret1_getelem ret2_getelem); done
  calc ret1[i] = listProduct (nums.take i) * listProduct (nums.drop (i + 1)) := ret1_val
    _ = ret2[i] := ret2_val.symm
end Proof
