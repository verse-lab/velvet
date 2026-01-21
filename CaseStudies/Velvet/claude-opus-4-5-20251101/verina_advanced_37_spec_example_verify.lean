import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def isMajorityElement (nums : List Int) (x : Int) : Prop :=
  nums.count x > nums.length / 2


def hasMajorityElement (nums : List Int) : Prop :=
  ∃ x ∈ nums, isMajorityElement nums x




def ensures1 (nums : List Int) (result : Int) :=
  result ∈ nums


def ensures2 (nums : List Int) (result : Int) :=
  nums.count result > nums.length / 2

def precondition (nums : List Int) :=
  nums.length > 0 ∧ hasMajorityElement nums

def postcondition (nums : List Int) (result : Int) :=
  ensures1 nums result ∧ ensures2 nums result


def test1_nums : List Int := [3, 2, 3]

def test1_Expected : Int := 3

def test2_nums : List Int := [2, 2, 1, 1, 1, 2, 2]

def test2_Expected : Int := 2

def test3_nums : List Int := [1]

def test3_Expected : Int := 1







section Proof
theorem test1_precondition :
  precondition test1_nums := by
  unfold precondition test1_nums hasMajorityElement isMajorityElement
  constructor
  · -- nums.length > 0
    native_decide
  · -- hasMajorityElement
    use 3
    constructor
    · -- 3 ∈ [3, 2, 3]
      simp [List.mem_cons]
    · -- [3, 2, 3].count 3 > [3, 2, 3].length / 2
      native_decide

theorem test1_postcondition :
  postcondition test1_nums test1_Expected := by
  unfold postcondition ensures1 ensures2 test1_nums test1_Expected
  constructor
  · native_decide
  · native_decide

theorem test2_precondition :
  precondition test2_nums := by
  unfold precondition test2_nums hasMajorityElement isMajorityElement
  constructor
  · native_decide
  · use 2
    constructor
    · native_decide
    · native_decide

theorem test2_postcondition :
  postcondition test2_nums test2_Expected := by
  unfold postcondition ensures1 ensures2 test2_nums test2_Expected
  native_decide

theorem test3_precondition :
  precondition test3_nums := by
  unfold precondition test3_nums hasMajorityElement isMajorityElement
  constructor
  · native_decide
  · use 1
    constructor
    · native_decide
    · native_decide

theorem test3_postcondition :
  postcondition test3_nums test3_Expected := by
  unfold postcondition ensures1 ensures2 test3_nums test3_Expected
  native_decide

theorem uniqueness (nums : List Int):
  precondition nums →
  (∀ ret1 ret2,
    postcondition nums ret1 →
    postcondition nums ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  unfold postcondition ensures1 ensures2 at hpost1 hpost2
  obtain ⟨_, hcount1⟩ := hpost1
  obtain ⟨_, hcount2⟩ := hpost2
  by_contra hne
  -- Key lemma: for distinct elements, sum of counts ≤ length
  have h_sum_le : nums.count ret1 + nums.count ret2 ≤ nums.length := by
    have count_sum_le : ∀ (l : List Int) (a b : Int), a ≠ b → l.count a + l.count b ≤ l.length := by
      intro l a b hab
      induction l with
      | nil => simp [List.count]
      | cons x xs ih =>
        simp only [List.count_cons, List.length_cons]
        have ih_applied := ih
        by_cases h1 : x = a <;> by_cases h2 : x = b
        · -- x = a and x = b, contradiction since a ≠ b
          subst h1 h2
          exact absurd rfl hab
        · -- x = a and x ≠ b
          have ha : (x == a) = true := by simp [h1]
          have hb : (x == b) = false := by simp [h2]
          simp only [ha, hb, ↓reduceIte]
          calc xs.count a + 1 + xs.count b 
              = xs.count a + xs.count b + 1 := by ring
            _ ≤ xs.length + 1 := by omega
        · -- x ≠ a and x = b
          have ha : (x == a) = false := by simp [h1]
          have hb : (x == b) = true := by simp [h2]
          simp only [ha, hb, ↓reduceIte]
          calc xs.count a + (xs.count b + 1) 
              = xs.count a + xs.count b + 1 := by ring
            _ ≤ xs.length + 1 := by omega
        · -- x ≠ a and x ≠ b
          have ha : (x == a) = false := by simp [h1]
          have hb : (x == b) = false := by simp [h2]
          simp only [ha, hb, ↓reduceIte]
          calc xs.count a + xs.count b 
              ≤ xs.length := ih_applied
            _ ≤ xs.length + 1 := by omega
    exact count_sum_le nums ret1 ret2 hne
  -- Now derive contradiction from arithmetic
  have h1 : nums.count ret1 ≥ nums.length / 2 + 1 := by omega
  have h2 : nums.count ret2 ≥ nums.length / 2 + 1 := by omega
  have h3 : nums.count ret1 + nums.count ret2 ≥ nums.length / 2 + 1 + (nums.length / 2 + 1) := by omega
  have h4 : nums.length / 2 + nums.length / 2 + 2 > nums.length := by
    have : nums.length / 2 * 2 ≤ nums.length := Nat.div_mul_le_self nums.length 2
    omega
  omega
end Proof
