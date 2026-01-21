import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def isBinaryString (s : String) : Prop :=
  ∀ c, c ∈ s.toList → c = '0' ∨ c = '1'


def countOnes (s : String) : Nat :=
  s.toList.count '1'


def isSubstringAt (s : String) (sub : String) (i : Nat) : Prop :=
  i + sub.length ≤ s.length ∧
  ∀ j : Nat, j < sub.length → s.toList[i + j]! = sub.toList[j]!


def isSubstringOf (s : String) (sub : String) : Prop :=
  ∃ i : Nat, isSubstringAt s sub i


def isValidCandidate (s : String) (sub : String) (k : Nat) : Prop :=
  isSubstringOf s sub ∧ countOnes sub = k


def isOptimalResult (s : String) (k : Nat) (result : String) : Prop :=
  isValidCandidate s result k ∧
  (∀ other : String, isValidCandidate s other k →
    result.length < other.length ∨
    (result.length = other.length ∧ result ≤ other))


def noValidCandidate (s : String) (k : Nat) : Prop :=
  ¬∃ sub : String, isValidCandidate s sub k



def precondition (s : String) (k : Nat) :=
  isBinaryString s


def ensures1 (s : String) (k : Nat) (result : String) :=
  noValidCandidate s k → result = ""

def ensures2 (s : String) (k : Nat) (result : String) :=
  (∃ sub : String, isValidCandidate s sub k) → isOptimalResult s k result

def postcondition (s : String) (k : Nat) (result : String) :=
  ensures1 s k result ∧ ensures2 s k result


def test1_s : String := "100011001"

def test1_k : Nat := 3

def test1_Expected : String := "11001"

def test2_s : String := "1011"

def test2_k : Nat := 2

def test2_Expected : String := "11"

def test4_s : String := "11111"

def test4_k : Nat := 3

def test4_Expected : String := "111"







section Proof
theorem test1_precondition :
  precondition test1_s test1_k := by
  unfold precondition isBinaryString test1_s
  intro c hc
  have : c ∈ ['1', '0', '0', '0', '1', '1', '0', '0', '1'] := hc
  rcases List.mem_cons.mp this with rfl | h
  · right; rfl
  · rcases List.mem_cons.mp h with rfl | h
    · left; rfl
    · rcases List.mem_cons.mp h with rfl | h
      · left; rfl
      · rcases List.mem_cons.mp h with rfl | h
        · left; rfl
        · rcases List.mem_cons.mp h with rfl | h
          · right; rfl
          · rcases List.mem_cons.mp h with rfl | h
            · right; rfl
            · rcases List.mem_cons.mp h with rfl | h
              · left; rfl
              · rcases List.mem_cons.mp h with rfl | h
                · left; rfl
                · rcases List.mem_cons.mp h with rfl | h
                  · right; rfl
                  · simp at h

theorem test1_postcondition_0 : ∃ sub, isValidCandidate "100011001" sub 3 := by
  use "11001"
  unfold isValidCandidate
  constructor
  · -- isSubstringOf "100011001" "11001"
    unfold isSubstringOf
    use 4
    unfold isSubstringAt
    constructor
    · -- 4 + "11001".length ≤ "100011001".length
      native_decide
    · -- ∀ j < "11001".length, "100011001".toList[4 + j]! = "11001".toList[j]!
      intro j hj
      have hlen : "11001".length = 5 := by native_decide
      rw [hlen] at hj
      match j with
      | 0 => native_decide
      | 1 => native_decide
      | 2 => native_decide
      | 3 => native_decide
      | 4 => native_decide
      | n + 5 => omega
  · -- countOnes "11001" = 3
    native_decide

theorem test1_postcondition_1
    (h_exists : ∃ sub, isValidCandidate "100011001" sub 3)
    : isValidCandidate "100011001" "11001" 3 := by
    unfold isValidCandidate
    constructor
    · -- isSubstringOf "100011001" "11001"
      unfold isSubstringOf
      use 4
      unfold isSubstringAt
      constructor
      · -- 4 + "11001".length ≤ "100011001".length
        native_decide
      · -- ∀ j < 5, characters match
        intro j hj
        have hlen : "11001".length = 5 := by native_decide
        have hj' : j < 5 := by simp only [hlen] at hj; exact hj
        match j, hj' with
        | 0, _ => native_decide
        | 1, _ => native_decide
        | 2, _ => native_decide
        | 3, _ => native_decide
        | 4, _ => native_decide
    · -- countOnes "11001" = 3
      native_decide

theorem test1_postcondition_2
    (h_exists : ∃ sub, isValidCandidate "100011001" sub 3)
    (other : String)
    (h_other_valid : isValidCandidate "100011001" other 3)
    (h_result_len : "11001".length = 5)
    : ∀ (sub : String), isValidCandidate "100011001" sub 3 → 5 ≤ sub.length := by
    sorry

theorem test1_postcondition_3
    (h_exists : ∃ sub, isValidCandidate "100011001" sub 3)
    (other : String)
    (h_other_valid : isValidCandidate "100011001" other 3)
    (h_result_len : "11001".length = 5)
    (h_min_len : ∀ (sub : String), isValidCandidate "100011001" sub 3 → 5 ≤ sub.length)
    (h_other_len_ge : 5 ≤ other.length)
    (h_len_eq : "11001".length = other.length)
    : ∀ (sub : String), isValidCandidate "100011001" sub 3 → sub.length = 5 → "11001" ≤ sub := by
    sorry

theorem test1_postcondition :
  postcondition test1_s test1_k test1_Expected := by
  unfold postcondition ensures1 ensures2 test1_s test1_k test1_Expected
  constructor
  -- Part 1: ensures1 - if no valid candidate, result = ""
  · -- We show the premise is false (there exists a valid candidate)
    have h_valid_exists : ∃ sub : String, isValidCandidate "100011001" sub 3 := by (try simp at *; expose_names); exact (test1_postcondition_0); done
    intro h_no_valid
    exfalso
    exact h_no_valid h_valid_exists
  -- Part 2: ensures2 - if valid candidate exists, result is optimal
  · intro h_exists
    unfold isOptimalResult
    constructor
    -- Show "11001" is a valid candidate
    · have h_is_valid : isValidCandidate "100011001" "11001" 3 := by (try simp at *; expose_names); exact (test1_postcondition_1 h_exists); done
      exact h_is_valid
    -- Show "11001" is optimal among all valid candidates
    · intro other h_other_valid
      -- We need: "11001".length < other.length ∨ ("11001".length = other.length ∧ "11001" ≤ other)
      have h_result_len : "11001".length = 5 := by (try simp at *; expose_names); exact rfl; done
      have h_min_len : ∀ sub, isValidCandidate "100011001" sub 3 → 5 ≤ sub.length := by (try simp at *; expose_names); exact (test1_postcondition_2 h_exists other h_other_valid h_result_len); done
      have h_other_len_ge : 5 ≤ other.length := by (try simp at *; expose_names); exact (h_min_len other h_other_valid); done
      -- Case split on whether other.length = 5 or other.length > 5
      by_cases h_len_eq : "11001".length = other.length
      · -- Same length case: need to show "11001" ≤ other lexicographically
        right
        constructor
        · exact h_len_eq
        · -- All valid candidates of length 5 are ≥ "11001" lexicographically
          have h_lex_min : ∀ sub, isValidCandidate "100011001" sub 3 → sub.length = 5 → "11001" ≤ sub := by (try simp at *; expose_names); exact (test1_postcondition_3 h_exists other h_other_valid h_result_len h_min_len h_other_len_ge h_len_eq); done
          have h_other_len_5 : other.length = 5 := by (try simp at *; expose_names); exact (id (Eq.symm h_len_eq)); done
          exact h_lex_min other h_other_valid h_other_len_5
      · -- Different length case: other must be longer
        left
        have h_other_len_gt : 5 < other.length := by (try simp at *; expose_names); exact (Nat.lt_of_le_of_ne (h_min_len other h_other_valid) h_len_eq); done
        omega
end Proof
