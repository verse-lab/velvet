import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def selectedProduct (nums : List Int) (selector : Nat → Bool) : Int :=
  (List.range nums.length).foldl 
    (fun acc i => if selector i then acc * nums[i]! else acc) 
    1


def isNonEmptySelection (nums : List Int) (selector : Nat → Bool) : Prop :=
  ∃ i : Nat, i < nums.length ∧ selector i = true


def isAchievable (nums : List Int) (result : Int) : Prop :=
  ∃ selector : Nat → Bool, 
    isNonEmptySelection nums selector ∧ 
    selectedProduct nums selector = result


def isMaximal (nums : List Int) (result : Int) : Prop :=
  ∀ selector : Nat → Bool, 
    isNonEmptySelection nums selector → 
    selectedProduct nums selector ≤ result



def precondition (nums : List Int) : Prop :=
  nums.length > 0



def postcondition (nums : List Int) (result : Int) : Prop :=
  isAchievable nums result ∧ isMaximal nums result


def test1_nums : List Int := [-2]

def test1_Expected : Int := -2

def test2_nums : List Int := [3, -1, -5, 2, 5, -9]

def test2_Expected : Int := 1350

def test4_nums : List Int := [0, -3, 4]

def test4_Expected : Int := 4







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  unfold precondition test1_nums
  decide

theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  unfold postcondition test1_nums test1_Expected
  constructor
  · -- isAchievable [-2] (-2)
    unfold isAchievable
    use fun _ => true
    constructor
    · -- isNonEmptySelection
      unfold isNonEmptySelection
      use 0
      simp [List.length]
    · -- selectedProduct equals -2
      unfold selectedProduct
      native_decide
  · -- isMaximal [-2] (-2)
    unfold isMaximal
    intro selector hsel
    unfold isNonEmptySelection at hsel
    obtain ⟨i, hi_lt, hi_sel⟩ := hsel
    -- Since list has length 1, i must be 0
    have hi_eq : i = 0 := by
      simp [List.length] at hi_lt
      omega
    -- The selectedProduct depends on whether selector 0 is true
    unfold selectedProduct
    simp only [List.length]
    -- With length 1, List.range 1 = [0]
    have hrange : List.range 1 = [0] := by native_decide
    simp only [hrange]
    simp only [List.foldl]
    -- If selector 0 = true, product is 1 * (-2) = -2
    -- If selector 0 = false, but we know some i < 1 has selector i = true
    -- Since i < 1 means i = 0, selector 0 must be true
    subst hi_eq
    simp only [hi_sel]
    native_decide

theorem test2_precondition :
  precondition test2_nums := by
  unfold precondition test2_nums
  decide

theorem test2_postcondition_0
    (selector : ℕ → Bool)
    (i : ℕ)
    (hi_sel : selector i = true)
    (h_range : List.range 6 = [0, 1, 2, 3, 4, 5])
    (h_bound : i < 6)
    (hi_lt : i < 6)
    (h_len : True)
    : (if selector 5 = true then -if selector 4 = true then if selector 3 = true then if selector 2 = true then -if selector 1 = true then -if selector 0 = true then 1350 else 450 else if selector 0 = true then 1350 else 450 else if selector 1 = true then -if selector 0 = true then 270 else 90 else if selector 0 = true then 270 else 90 else if selector 2 = true then -if selector 1 = true then -if selector 0 = true then 675 else 225 else if selector 0 = true then 675 else 225 else if selector 1 = true then -if selector 0 = true then 135 else 45 else if selector 0 = true then 135 else 45 else if selector 3 = true then if selector 2 = true then -if selector 1 = true then -if selector 0 = true then 270 else 90 else if selector 0 = true then 270 else 90 else if selector 1 = true then -if selector 0 = true then 54 else 18 else if selector 0 = true then 54 else 18 else if selector 2 = true then -if selector 1 = true then -if selector 0 = true then 135 else 45 else if selector 0 = true then 135 else 45 else if selector 1 = true then -if selector 0 = true then 27 else 9 else if selector 0 = true then 27 else 9 else if selector 4 = true then if selector 3 = true then if selector 2 = true then -if selector 1 = true then -if selector 0 = true then 150 else 50 else if selector 0 = true then 150 else 50 else if selector 1 = true then -if selector 0 = true then 30 else 10 else if selector 0 = true then 30 else 10 else if selector 2 = true then -if selector 1 = true then -if selector 0 = true then 75 else 25 else if selector 0 = true then 75 else 25 else if selector 1 = true then -if selector 0 = true then 15 else 5 else if selector 0 = true then 15 else 5 else if selector 3 = true then if selector 2 = true then -if selector 1 = true then -if selector 0 = true then 30 else 10 else if selector 0 = true then 30 else 10 else if selector 1 = true then -if selector 0 = true then 6 else 2 else if selector 0 = true then 6 else 2 else if selector 2 = true then -if selector 1 = true then -if selector 0 = true then 15 else 5 else if selector 0 = true then 15 else 5 else if selector 1 = true then -if selector 0 = true then 3 else 1 else if selector 0 = true then 3 else 1) ≤ 1350 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test2_postcondition :
  postcondition test2_nums test2_Expected := by
  unfold postcondition test2_nums test2_Expected
  constructor
  · -- isAchievable [3, -1, -5, 2, 5, -9] 1350
    unfold isAchievable
    -- Use selector that selects all indices except 1 (the -1)
    have h_selector : ∃ selector : Nat → Bool, isNonEmptySelection [3, -1, -5, 2, 5, -9] selector ∧ selectedProduct [3, -1, -5, 2, 5, -9] selector = 1350 := by
      use fun i => i != 1
      constructor
      · -- isNonEmptySelection
        unfold isNonEmptySelection
        use 0
        simp [List.length]
      · -- selectedProduct equals 1350
        unfold selectedProduct
        native_decide
    exact h_selector
  · -- isMaximal [3, -1, -5, 2, 5, -9] 1350
    unfold isMaximal
    intro selector hsel
    unfold isNonEmptySelection at hsel
    obtain ⟨i, hi_lt, hi_sel⟩ := hsel
    -- The list has length 6, so there are 2^6 - 1 = 63 possible non-empty selections
    -- We need to show all of them have product ≤ 1350
    unfold selectedProduct
    have h_len : [3, -1, -5, 2, 5, -9].length = 6 := by native_decide
    -- The foldl computation over List.range 6 can be verified computationally
    -- For any valid selector with at least one true value at index < 6,
    -- the product is at most 1350
    have h_range : List.range 6 = [0, 1, 2, 3, 4, 5] := by native_decide
    simp only [h_len, h_range]
    -- This requires case analysis on all possible selector values
    -- Since selector is a function Nat → Bool, we evaluate based on selector's values at 0,1,2,3,4,5
    have h_bound : i < 6 := by simp [List.length] at hi_lt; exact hi_lt
    -- The proof requires showing that for any boolean assignment to indices 0-5 with at least one true,
    -- the resulting product is ≤ 1350
    -- Maximum positive product is achieved by excluding -1 (index 1): 3 × (-5) × 2 × 5 × (-9) = 1350
    -- All other selections either have smaller magnitude or are negative
    have h_cases : List.foldl (fun acc i => if selector i = true then acc * [3, -1, -5, 2, 5, -9][i]! else acc) 1 [0, 1, 2, 3, 4, 5] ≤ 1350 := by
      (try simp at *; expose_names); exact (test2_postcondition_0 selector i hi_sel h_range h_bound hi_lt h_len); done
    exact h_cases

theorem test4_precondition : precondition test4_nums := by
  unfold precondition test4_nums
  decide

theorem test4_postcondition :
  postcondition test4_nums test4_Expected := by
  unfold postcondition test4_nums test4_Expected
  constructor
  · -- isAchievable: show 4 can be achieved
    unfold isAchievable
    use fun i => i == 2
    constructor
    · -- isNonEmptySelection
      unfold isNonEmptySelection
      use 2
      simp
    · -- selectedProduct equals 4
      native_decide
  · -- isMaximal: show all products ≤ 4
    unfold isMaximal
    intro selector h_nonempty
    unfold isNonEmptySelection at h_nonempty
    obtain ⟨i, hi_bound, hi_sel⟩ := h_nonempty
    unfold selectedProduct
    simp only [List.length]
    have h_range : List.range 3 = [0, 1, 2] := by native_decide
    rw [h_range]
    simp only [List.foldl]
    -- Case analysis on selector values at indices 0, 1, 2
    have h_i_bound : i < 3 := hi_bound
    interval_cases i
    · -- i = 0
      simp only [hi_sel]
      cases h1 : selector 1 <;> cases h2 : selector 2 <;> simp [h1, h2] <;> decide
    · -- i = 1
      simp only [hi_sel]
      cases h0 : selector 0 <;> cases h2 : selector 2 <;> simp [h0, h2] <;> decide
    · -- i = 2
      simp only [hi_sel]
      cases h0 : selector 0 <;> cases h1 : selector 1 <;> simp [h0, h1] <;> decide

theorem uniqueness (nums : List Int):
  precondition nums →
  (∀ ret1 ret2,
    postcondition nums ret1 →
    postcondition nums ret2 →
    ret1 = ret2) := by
  intro _hpre ret1 ret2 hpost1 hpost2
  -- Unpack postconditions
  obtain ⟨hachievable1, hmaximal1⟩ := hpost1
  obtain ⟨hachievable2, hmaximal2⟩ := hpost2
  -- Unpack achievability to get the selectors
  obtain ⟨selector1, hnonempty1, hprod1⟩ := hachievable1
  obtain ⟨selector2, hnonempty2, hprod2⟩ := hachievable2
  -- Use maximality to get inequalities
  -- hmaximal2 says all products ≤ ret2, apply to selector1
  have h1 : ret1 ≤ ret2 := by
    have := hmaximal2 selector1 hnonempty1
    rw [hprod1] at this
    exact this
  -- hmaximal1 says all products ≤ ret1, apply to selector2
  have h2 : ret2 ≤ ret1 := by
    have := hmaximal1 selector2 hnonempty2
    rw [hprod2] at this
    exact this
  -- Conclude by antisymmetry
  exact Int.le_antisymm h1 h2
end Proof
