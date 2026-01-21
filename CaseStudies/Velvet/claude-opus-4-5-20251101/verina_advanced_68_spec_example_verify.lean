import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def isDigitChar (c : Char) : Bool := c.isDigit


def noDigitsInString (s : String) : Prop :=
  ∀ c, c ∈ s.toList → ¬isDigitChar c



def expandRun (c : Char) (n : Nat) : List Char :=
  List.replicate n c


def expandRuns (runs : List (Char × Nat)) : List Char :=
  runs.flatMap (fun p => expandRun p.1 p.2)


def encodeRun (c : Char) (n : Nat) : List Char :=
  c :: (Nat.repr n).toList


def encodeRuns (runs : List (Char × Nat)) : List Char :=
  runs.flatMap (fun p => encodeRun p.1 p.2)


def validRunCounts (runs : List (Char × Nat)) : Prop :=
  ∀ i : Nat, i < runs.length → (runs[i]!).2 ≥ 1


def maximalRuns (runs : List (Char × Nat)) : Prop :=
  ∀ i : Nat, i + 1 < runs.length → (runs[i]!).1 ≠ (runs[i+1]!).1


def runsNoDigits (runs : List (Char × Nat)) : Prop :=
  ∀ i : Nat, i < runs.length → ¬isDigitChar (runs[i]!).1



def decodeRLE (runs : List (Char × Nat)) : List Char :=
  runs.flatMap (fun p => List.replicate p.2 p.1)








def ensures1 (input : String) (result : String) :=
  ∃ (runs : List (Char × Nat)),

    expandRuns runs = input.toList ∧

    validRunCounts runs ∧

    maximalRuns runs ∧

    runsNoDigits runs ∧

    result.toList = encodeRuns runs


def ensures2 (input : String) (result : String) :=
  (input.isEmpty ↔ result.isEmpty)



def precondition (input : String) :=
  noDigitsInString input



def postcondition (input : String) (result : String) :=
  ensures1 input result ∧ ensures2 input result


def test1_input : String := "aaabbbcc"

def test1_Expected : String := "a3b3c2"

def test4_input : String := "abcd"

def test4_Expected : String := "a1b1c1d1"

def test5_input : String := ""

def test5_Expected : String := ""







section Proof
theorem test1_precondition :
  precondition test1_input := by
  unfold precondition noDigitsInString test1_input isDigitChar
  intro c hc
  simp only [String.toList] at hc
  fin_cases hc <;> native_decide

theorem test1_postcondition :
  postcondition test1_input test1_Expected := by
  unfold postcondition ensures1 ensures2 test1_input test1_Expected
  constructor
  · -- ensures1
    use [('a', 3), ('b', 3), ('c', 2)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- expandRuns runs = input.toList
      native_decide
    · -- validRunCounts runs
      unfold validRunCounts
      intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      match i with
      | 0 => simp [List.getElem!_cons_zero]
      | 1 => simp [List.getElem!_cons_succ, List.getElem!_cons_zero]
      | 2 => simp [List.getElem!_cons_succ, List.getElem!_cons_zero]
      | n + 3 => omega
    · -- maximalRuns runs
      unfold maximalRuns
      intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      match i with
      | 0 => simp [List.getElem!_cons_zero, List.getElem!_cons_succ]
      | 1 => simp [List.getElem!_cons_succ, List.getElem!_cons_zero]
      | n + 2 => omega
    · -- runsNoDigits runs
      unfold runsNoDigits isDigitChar
      intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      match i with
      | 0 => native_decide
      | 1 => native_decide
      | 2 => native_decide
      | n + 3 => omega
    · -- result.toList = encodeRuns runs
      native_decide
  · -- ensures2: input.isEmpty ↔ result.isEmpty
    native_decide

theorem test4_precondition :
  precondition test4_input := by
  unfold precondition noDigitsInString test4_input isDigitChar
  intro c hc
  fin_cases hc <;> native_decide

theorem test4_postcondition :
  postcondition test4_input test4_Expected := by
  unfold postcondition ensures1 ensures2
  constructor
  · -- ensures1
    use [('a', 1), ('b', 1), ('c', 1), ('d', 1)]
    constructor
    · native_decide
    constructor
    · unfold validRunCounts
      intro i hi
      simp only [List.length] at hi
      match i with
      | 0 => native_decide
      | 1 => native_decide
      | 2 => native_decide
      | 3 => native_decide
    constructor
    · unfold maximalRuns
      intro i hi
      simp only [List.length] at hi
      match i with
      | 0 => native_decide
      | 1 => native_decide
      | 2 => native_decide
    constructor
    · unfold runsNoDigits isDigitChar
      intro i hi
      simp only [List.length] at hi
      match i with
      | 0 => native_decide
      | 1 => native_decide
      | 2 => native_decide
      | 3 => native_decide
    · native_decide
  · native_decide

theorem test5_precondition :
  precondition test5_input := by
  unfold precondition noDigitsInString test5_input
  intro c hc
  exact absurd hc (List.not_mem_nil)

theorem test5_postcondition :
  postcondition test5_input test5_Expected := by
  unfold postcondition ensures1 ensures2 test5_input test5_Expected
  constructor
  · -- ensures1: need to provide witness runs = []
    use []
    constructor
    · -- expandRuns [] = "".toList
      native_decide
    constructor
    · -- validRunCounts []
      unfold validRunCounts
      intro i hi
      simp [List.length] at hi
    constructor
    · -- maximalRuns []
      unfold maximalRuns
      intro i hi
      simp [List.length] at hi
    constructor
    · -- runsNoDigits []
      unfold runsNoDigits
      intro i hi
      simp [List.length] at hi
    · -- "".toList = encodeRuns []
      native_decide
  · -- ensures2: "".isEmpty ↔ "".isEmpty
    constructor <;> intro h <;> exact h

theorem uniqueness_0
    (input : String)
    (hpre : precondition input)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition input ret1)
    (hpost2 : postcondition input ret2)
    : ensures1 input ret1 := by
    exact hpost1.1

theorem uniqueness_1
    (input : String)
    (hpre : precondition input)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition input ret1)
    (hpost2 : postcondition input ret2)
    (h1_ensures1 : ensures1 input ret1)
    : ensures1 input ret2 := by
    intros; expose_names; exact (uniqueness_0 input hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_2_1
    (input : String)
    (hpre : precondition input)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition input ret1)
    (hpost2 : postcondition input ret2)
    (h1_ensures1 : ensures1 input ret1)
    (h2_ensures1 : ensures1 input ret2)
    (h1_runs : ∃ runs1, expandRuns runs1 = input.data ∧ validRunCounts runs1 ∧ maximalRuns runs1 ∧ runsNoDigits runs1 ∧ ret1.data = encodeRuns runs1)
    (h2_runs : ∃ runs2, expandRuns runs2 = input.data ∧ validRunCounts runs2 ∧ maximalRuns runs2 ∧ runsNoDigits runs2 ∧ ret2.data = encodeRuns runs2)
    (h_unique_general : ∀ (s : List Char) (r1 r2 : List (Char × ℕ)), expandRuns r1 = s → expandRuns r2 = s → validRunCounts r1 → validRunCounts r2 → maximalRuns r1 → maximalRuns r2 → r1 = r2)
    (h_expandRuns_nil : expandRuns [] = [])
    (h_expandRuns_cons : ∀ (c : Char) (n : ℕ) (tail : List (Char × ℕ)), expandRuns ((c, n) :: tail) = List.replicate n c ++ expandRuns tail)
    (h_replicate_pos_ne_nil : ∀ (n : ℕ), 1 ≤ n → ¬n = 0)
    : ∀ (runs : List (Char × ℕ)) (i : ℕ), validRunCounts runs → i < runs.length → 1 ≤ (runs[i]?.getD default).2 := by
  intro runs i hvalid hi
  unfold validRunCounts at hvalid
  have h := hvalid i hi
  have h_eq : runs[i]?.getD default = runs[i]! := by
    rw [List.getElem!_eq_getElem?_getD]
  rw [h_eq]
  exact h

theorem uniqueness_2_2
    (input : String)
    (hpre : precondition input)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition input ret1)
    (hpost2 : postcondition input ret2)
    (h1_ensures1 : ensures1 input ret1)
    (h2_ensures1 : ensures1 input ret2)
    (h1_runs : ∃ runs1, expandRuns runs1 = input.data ∧ validRunCounts runs1 ∧ maximalRuns runs1 ∧ runsNoDigits runs1 ∧ ret1.data = encodeRuns runs1)
    (h2_runs : ∃ runs2, expandRuns runs2 = input.data ∧ validRunCounts runs2 ∧ maximalRuns runs2 ∧ runsNoDigits runs2 ∧ ret2.data = encodeRuns runs2)
    (h_unique_general : ∀ (s : List Char) (r1 r2 : List (Char × ℕ)), expandRuns r1 = s → expandRuns r2 = s → validRunCounts r1 → validRunCounts r2 → maximalRuns r1 → maximalRuns r2 → r1 = r2)
    (h_expandRuns_nil : expandRuns [] = [])
    (h_expandRuns_cons : ∀ (c : Char) (n : ℕ) (tail : List (Char × ℕ)), expandRuns ((c, n) :: tail) = List.replicate n c ++ expandRuns tail)
    (h_nonempty_expand_implies_nonempty_runs : ∀ (runs : List (Char × ℕ)), validRunCounts runs → ¬expandRuns runs = [] → ¬runs = [])
    (h_replicate_pos_ne_nil : ∀ (n : ℕ), 1 ≤ n → ¬n = 0)
    (h_valid_implies_nonempty_run : ∀ (runs : List (Char × ℕ)) (i : ℕ), validRunCounts runs → i < runs.length → 1 ≤ (runs[i]?.getD default).2)
    : ∀ (c : Char) (n : ℕ) (tail : List (Char × ℕ)), 1 ≤ n → (List.replicate n c).head? = some c ∨ n = 0 ∧ (expandRuns tail).head? = some c := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_2_3
    (input : String)
    (hpre : precondition input)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition input ret1)
    (hpost2 : postcondition input ret2)
    (h1_ensures1 : ensures1 input ret1)
    (h2_ensures1 : ensures1 input ret2)
    (h1_runs : ∃ runs1, expandRuns runs1 = input.data ∧ validRunCounts runs1 ∧ maximalRuns runs1 ∧ runsNoDigits runs1 ∧ ret1.data = encodeRuns runs1)
    (h2_runs : ∃ runs2, expandRuns runs2 = input.data ∧ validRunCounts runs2 ∧ maximalRuns runs2 ∧ runsNoDigits runs2 ∧ ret2.data = encodeRuns runs2)
    (h_unique_general : ∀ (s : List Char) (r1 r2 : List (Char × ℕ)), expandRuns r1 = s → expandRuns r2 = s → validRunCounts r1 → validRunCounts r2 → maximalRuns r1 → maximalRuns r2 → r1 = r2)
    (h_expandRuns_nil : expandRuns [] = [])
    (h_expandRuns_cons : ∀ (c : Char) (n : ℕ) (tail : List (Char × ℕ)), expandRuns ((c, n) :: tail) = List.replicate n c ++ expandRuns tail)
    (h_nonempty_expand_implies_nonempty_runs : ∀ (runs : List (Char × ℕ)), validRunCounts runs → ¬expandRuns runs = [] → ¬runs = [])
    (h_replicate_pos_ne_nil : ∀ (n : ℕ), 1 ≤ n → ¬n = 0)
    (h_valid_implies_nonempty_run : ∀ (runs : List (Char × ℕ)) (i : ℕ), validRunCounts runs → i < runs.length → 1 ≤ (runs[i]?.getD default).2)
    (h_first_char_determines_first_run_char : ∀ (c : Char) (n : ℕ) (tail : List (Char × ℕ)), 1 ≤ n → (List.replicate n c).head? = some c ∨ n = 0 ∧ (expandRuns tail).head? = some c)
    : ∀ (r1 r2 : List (Char × ℕ)) (c : Char) (n1 n2 : ℕ) (t1 t2 : List (Char × ℕ)), r1 = (c, n1) :: t1 → r2 = (c, n2) :: t2 → expandRuns r1 = expandRuns r2 → validRunCounts r1 → validRunCounts r2 → maximalRuns r1 → maximalRuns r2 → n1 = n2 := by
  intro r1 r2 c n1 n2 t1 t2 hr1 hr2 hexp hvalid1 hvalid2 hmax1 hmax2
  -- Use h_unique_general to show r1 = r2
  have heq : r1 = r2 := h_unique_general (expandRuns r1) r1 r2 rfl hexp.symm hvalid1 hvalid2 hmax1 hmax2
  -- From r1 = r2 and the definitions, we get n1 = n2
  rw [hr1, hr2] at heq
  have h_pair_eq : (c, n1) = (c, n2) := List.cons.inj heq |>.1
  exact Prod.mk.inj h_pair_eq |>.2

theorem uniqueness_2_4
    (input : String)
    (hpre : precondition input)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition input ret1)
    (hpost2 : postcondition input ret2)
    (h1_ensures1 : ensures1 input ret1)
    (h2_ensures1 : ensures1 input ret2)
    (h1_runs : ∃ runs1, expandRuns runs1 = input.data ∧ validRunCounts runs1 ∧ maximalRuns runs1 ∧ runsNoDigits runs1 ∧ ret1.data = encodeRuns runs1)
    (h2_runs : ∃ runs2, expandRuns runs2 = input.data ∧ validRunCounts runs2 ∧ maximalRuns runs2 ∧ runsNoDigits runs2 ∧ ret2.data = encodeRuns runs2)
    (h_unique_general : ∀ (s : List Char) (r1 r2 : List (Char × ℕ)), expandRuns r1 = s → expandRuns r2 = s → validRunCounts r1 → validRunCounts r2 → maximalRuns r1 → maximalRuns r2 → r1 = r2)
    (h_expandRuns_nil : expandRuns [] = [])
    (h_expandRuns_cons : ∀ (c : Char) (n : ℕ) (tail : List (Char × ℕ)), expandRuns ((c, n) :: tail) = List.replicate n c ++ expandRuns tail)
    (h_nonempty_expand_implies_nonempty_runs : ∀ (runs : List (Char × ℕ)), validRunCounts runs → ¬expandRuns runs = [] → ¬runs = [])
    (h_maximal_first_run_length : ∀ (r1 r2 : List (Char × ℕ)) (c : Char) (n1 n2 : ℕ) (t1 t2 : List (Char × ℕ)), r1 = (c, n1) :: t1 → r2 = (c, n2) :: t2 → expandRuns r1 = expandRuns r2 → validRunCounts r1 → validRunCounts r2 → maximalRuns r1 → maximalRuns r2 → n1 = n2)
    (h_replicate_pos_ne_nil : ∀ (n : ℕ), 1 ≤ n → ¬n = 0)
    (h_valid_implies_nonempty_run : ∀ (runs : List (Char × ℕ)) (i : ℕ), validRunCounts runs → i < runs.length → 1 ≤ (runs[i]?.getD default).2)
    (h_first_char_determines_first_run_char : ∀ (c : Char) (n : ℕ) (tail : List (Char × ℕ)), 1 ≤ n → (List.replicate n c).head? = some c ∨ n = 0 ∧ (expandRuns tail).head? = some c)
    (h_tail_expansion_eq : True)
    : ∀ (a : Char) (b : ℕ) (tail : List (Char × ℕ)), validRunCounts ((a, b) :: tail) → validRunCounts tail := by
  intro a b tail hvalid
  unfold validRunCounts at *
  intro i hi
  have hi' : i + 1 < ((a, b) :: tail).length := by
    simp [List.length_cons]
    omega
  have hcons := hvalid (i + 1) hi'
  rw [List.getElem!_cons_succ] at hcons
  exact hcons

theorem uniqueness_2_5
    (input : String)
    (hpre : precondition input)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition input ret1)
    (hpost2 : postcondition input ret2)
    (h1_ensures1 : ensures1 input ret1)
    (h2_ensures1 : ensures1 input ret2)
    (h1_runs : ∃ runs1, expandRuns runs1 = input.data ∧ validRunCounts runs1 ∧ maximalRuns runs1 ∧ runsNoDigits runs1 ∧ ret1.data = encodeRuns runs1)
    (h2_runs : ∃ runs2, expandRuns runs2 = input.data ∧ validRunCounts runs2 ∧ maximalRuns runs2 ∧ runsNoDigits runs2 ∧ ret2.data = encodeRuns runs2)
    (h_unique_general : ∀ (s : List Char) (r1 r2 : List (Char × ℕ)), expandRuns r1 = s → expandRuns r2 = s → validRunCounts r1 → validRunCounts r2 → maximalRuns r1 → maximalRuns r2 → r1 = r2)
    (h_expandRuns_nil : expandRuns [] = [])
    (h_expandRuns_cons : ∀ (c : Char) (n : ℕ) (tail : List (Char × ℕ)), expandRuns ((c, n) :: tail) = List.replicate n c ++ expandRuns tail)
    (h_nonempty_expand_implies_nonempty_runs : ∀ (runs : List (Char × ℕ)), validRunCounts runs → ¬expandRuns runs = [] → ¬runs = [])
    (h_maximal_first_run_length : ∀ (r1 r2 : List (Char × ℕ)) (c : Char) (n1 n2 : ℕ) (t1 t2 : List (Char × ℕ)), r1 = (c, n1) :: t1 → r2 = (c, n2) :: t2 → expandRuns r1 = expandRuns r2 → validRunCounts r1 → validRunCounts r2 → maximalRuns r1 → maximalRuns r2 → n1 = n2)
    (h_replicate_pos_ne_nil : ∀ (n : ℕ), 1 ≤ n → ¬n = 0)
    (h_valid_implies_nonempty_run : ∀ (runs : List (Char × ℕ)) (i : ℕ), validRunCounts runs → i < runs.length → 1 ≤ (runs[i]?.getD default).2)
    (h_first_char_determines_first_run_char : ∀ (c : Char) (n : ℕ) (tail : List (Char × ℕ)), 1 ≤ n → (List.replicate n c).head? = some c ∨ n = 0 ∧ (expandRuns tail).head? = some c)
    (h_tail_expansion_eq : True)
    (h_tail_valid : ∀ (a : Char) (b : ℕ) (tail : List (Char × ℕ)), validRunCounts ((a, b) :: tail) → validRunCounts tail)
    : ∀ (a : Char) (b : ℕ) (tail : List (Char × ℕ)), maximalRuns ((a, b) :: tail) → maximalRuns tail := by
    intro a b tail hmax
    unfold maximalRuns at hmax ⊢
    intro i hi
    have hi' : (i + 1) + 1 < ((a, b) :: tail).length := by
      simp [List.length_cons]
      omega
    have h := hmax (i + 1) hi'
    simp only [List.length_cons] at h
    have eq1 : ((a, b) :: tail)[i + 1]! = tail[i]! := by
      rw [List.getElem!_cons_succ]
    have eq2 : ((a, b) :: tail)[i + 1 + 1]! = tail[i + 1]! := by
      rw [List.getElem!_cons_succ]
    rw [eq1, eq2] at h
    exact h

theorem uniqueness_2_0
    (input : String)
    (hpre : precondition input)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition input ret1)
    (hpost2 : postcondition input ret2)
    (h1_ensures1 : ensures1 input ret1)
    (h2_ensures1 : ensures1 input ret2)
    (h1_runs : ∃ runs1, expandRuns runs1 = input.data ∧ validRunCounts runs1 ∧ maximalRuns runs1 ∧ runsNoDigits runs1 ∧ ret1.data = encodeRuns runs1)
    (h2_runs : ∃ runs2, expandRuns runs2 = input.data ∧ validRunCounts runs2 ∧ maximalRuns runs2 ∧ runsNoDigits runs2 ∧ ret2.data = encodeRuns runs2)
    : ∀ (s : List Char) (r1 r2 : List (Char × ℕ)), expandRuns r1 = s → expandRuns r2 = s → validRunCounts r1 → validRunCounts r2 → maximalRuns r1 → maximalRuns r2 → r1 = r2 := by
    sorry

theorem uniqueness_2
    (input : String)
    (hpre : precondition input)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition input ret1)
    (hpost2 : postcondition input ret2)
    (h1_ensures1 : ensures1 input ret1)
    (h2_ensures1 : ensures1 input ret2)
    (h1_runs : ∃ runs1, expandRuns runs1 = input.data ∧ validRunCounts runs1 ∧ maximalRuns runs1 ∧ runsNoDigits runs1 ∧ ret1.data = encodeRuns runs1)
    (h2_runs : ∃ runs2, expandRuns runs2 = input.data ∧ validRunCounts runs2 ∧ maximalRuns runs2 ∧ runsNoDigits runs2 ∧ ret2.data = encodeRuns runs2)
    : ∀ (runs1 runs2 : List (Char × ℕ)), expandRuns runs1 = input.data → expandRuns runs2 = input.data → validRunCounts runs1 → validRunCounts runs2 → maximalRuns runs1 → maximalRuns runs2 → runs1 = runs2 := by
    have h_unique_general : ∀ (s : List Char) (r1 r2 : List (Char × ℕ)), 
      expandRuns r1 = s → expandRuns r2 = s → 
      validRunCounts r1 → validRunCounts r2 → 
      maximalRuns r1 → maximalRuns r2 → r1 = r2 := by (try simp at *; expose_names); exact (uniqueness_2_0 input hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h2_ensures1 h1_runs h2_runs); done
    have h_expandRuns_nil : expandRuns [] = [] := by (try simp at *; expose_names); exact rfl; done
    have h_expandRuns_cons : ∀ (c : Char) (n : ℕ) (tail : List (Char × ℕ)), 
      expandRuns ((c, n) :: tail) = List.replicate n c ++ expandRuns tail := by (try simp at *; expose_names); exact (fun c n tail ↦ rfl); done
    have h_replicate_pos_ne_nil : ∀ (c : Char) (n : ℕ), n ≥ 1 → List.replicate n c ≠ [] := by (try simp at *; expose_names); exact (fun n a ↦ Nat.ne_zero_of_lt a); done
    have h_valid_implies_nonempty_run : ∀ (runs : List (Char × ℕ)) (i : ℕ), 
      validRunCounts runs → i < runs.length → (runs[i]!).2 ≥ 1 := by (try simp at *; expose_names); exact (uniqueness_2_1 input hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h2_ensures1 h1_runs h2_runs h_unique_general h_expandRuns_nil h_expandRuns_cons h_replicate_pos_ne_nil); done
    have h_nonempty_expand_implies_nonempty_runs : ∀ (runs : List (Char × ℕ)), 
      validRunCounts runs → expandRuns runs ≠ [] → runs ≠ [] := by (try simp at *; expose_names); exact (fun runs a a ↦ ne_of_apply_ne expandRuns a); done
    have h_first_char_determines_first_run_char : ∀ (c : Char) (n : ℕ) (tail : List (Char × ℕ)),
      n ≥ 1 → (List.replicate n c ++ expandRuns tail).head? = some c := by (try simp at *; expose_names); exact (uniqueness_2_2 input hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h2_ensures1 h1_runs h2_runs h_unique_general h_expandRuns_nil h_expandRuns_cons h_nonempty_expand_implies_nonempty_runs h_replicate_pos_ne_nil h_valid_implies_nonempty_run); done
    have h_maximal_first_run_length : ∀ (r1 r2 : List (Char × ℕ)) (c : Char) (n1 n2 : ℕ) (t1 t2 : List (Char × ℕ)),
      r1 = (c, n1) :: t1 → r2 = (c, n2) :: t2 →
      expandRuns r1 = expandRuns r2 →
      validRunCounts r1 → validRunCounts r2 →
      maximalRuns r1 → maximalRuns r2 →
      n1 = n2 := by (try simp at *; expose_names); exact (uniqueness_2_3 input hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h2_ensures1 h1_runs h2_runs h_unique_general h_expandRuns_nil h_expandRuns_cons h_nonempty_expand_implies_nonempty_runs h_replicate_pos_ne_nil h_valid_implies_nonempty_run h_first_char_determines_first_run_char); done
    have h_tail_expansion_eq : ∀ (c : Char) (n : ℕ) (t1 t2 : List (Char × ℕ)),
      List.replicate n c ++ expandRuns t1 = List.replicate n c ++ expandRuns t2 →
      expandRuns t1 = expandRuns t2 := by (try simp at *; expose_names); exact fun c n t1 t2 a ↦ (List.append_cancel_left a); done
    have h_tail_valid : ∀ (p : Char × ℕ) (tail : List (Char × ℕ)),
      validRunCounts (p :: tail) → validRunCounts tail := by (try simp at *; expose_names); exact (uniqueness_2_4 input hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h2_ensures1 h1_runs h2_runs h_unique_general h_expandRuns_nil h_expandRuns_cons h_nonempty_expand_implies_nonempty_runs h_maximal_first_run_length h_replicate_pos_ne_nil h_valid_implies_nonempty_run h_first_char_determines_first_run_char h_tail_expansion_eq); done
    have h_tail_maximal : ∀ (p : Char × ℕ) (tail : List (Char × ℕ)),
      maximalRuns (p :: tail) → maximalRuns tail := by (try simp at *; expose_names); exact (uniqueness_2_5 input hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h2_ensures1 h1_runs h2_runs h_unique_general h_expandRuns_nil h_expandRuns_cons h_nonempty_expand_implies_nonempty_runs h_maximal_first_run_length h_replicate_pos_ne_nil h_valid_implies_nonempty_run h_first_char_determines_first_run_char h_tail_expansion_eq h_tail_valid); done
    intro runs1 runs2 hexp1 hexp2 hvalid1 hvalid2 hmax1 hmax2
    exact h_unique_general input.data runs1 runs2 hexp1 hexp2 hvalid1 hvalid2 hmax1 hmax2

theorem uniqueness_3
    (input : String)
    (hpre : precondition input)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition input ret1)
    (hpost2 : postcondition input ret2)
    (h1_ensures1 : ensures1 input ret1)
    (h2_ensures1 : ensures1 input ret2)
    (runs_unique : ∀ (runs1 runs2 : List (Char × ℕ)), expandRuns runs1 = input.data → expandRuns runs2 = input.data → validRunCounts runs1 → validRunCounts runs2 → maximalRuns runs1 → maximalRuns runs2 → runs1 = runs2)
    (runs1 : List (Char × ℕ))
    (hexp1 : expandRuns runs1 = input.data)
    (hvalid1 : validRunCounts runs1)
    (hmax1 : maximalRuns runs1)
    (hnodig1 : runsNoDigits runs1)
    (hret1 : ret1.data = encodeRuns runs1)
    (runs2 : List (Char × ℕ))
    (hexp2 : expandRuns runs2 = input.data)
    (hvalid2 : validRunCounts runs2)
    (hmax2 : maximalRuns runs2)
    (hnodig2 : runsNoDigits runs2)
    (hret2 : ret2.data = encodeRuns runs2)
    (encode_eq : True)
    : runs1 = runs2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_4
    (input : String)
    (hpre : precondition input)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition input ret1)
    (hpost2 : postcondition input ret2)
    (h1_ensures1 : ensures1 input ret1)
    (h2_ensures1 : ensures1 input ret2)
    (runs_unique : ∀ (runs1 runs2 : List (Char × ℕ)), expandRuns runs1 = input.data → expandRuns runs2 = input.data → validRunCounts runs1 → validRunCounts runs2 → maximalRuns runs1 → maximalRuns runs2 → runs1 = runs2)
    (runs1 : List (Char × ℕ))
    (hexp1 : expandRuns runs1 = input.data)
    (hvalid1 : validRunCounts runs1)
    (hmax1 : maximalRuns runs1)
    (hnodig1 : runsNoDigits runs1)
    (hret1 : ret1.data = encodeRuns runs1)
    (runs2 : List (Char × ℕ))
    (hexp2 : expandRuns runs2 = input.data)
    (hvalid2 : validRunCounts runs2)
    (hmax2 : maximalRuns runs2)
    (hnodig2 : runsNoDigits runs2)
    (hret2 : ret2.data = encodeRuns runs2)
    (runs_eq : runs1 = runs2)
    (enc_eq : encodeRuns runs1 = encodeRuns runs2)
    (encode_eq : True)
    : ret1.data = ret2.data := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness (input : String):
  precondition input →
  (∀ ret1 ret2,
    postcondition input ret1 →
    postcondition input ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  -- Extract the ensures1 parts from both postconditions
  have h1_ensures1 : ensures1 input ret1 := by (try simp at *; expose_names); exact (uniqueness_0 input hpre ret1 ret2 hpost1 hpost2); done
  have h2_ensures1 : ensures1 input ret2 := by (try simp at *; expose_names); exact (uniqueness_1 input hpre ret1 ret2 hpost1 hpost2 h1_ensures1); done
  -- Get the witness runs from ensures1
  have h1_runs : ∃ runs1 : List (Char × Nat), expandRuns runs1 = input.toList ∧ validRunCounts runs1 ∧ maximalRuns runs1 ∧ runsNoDigits runs1 ∧ ret1.toList = encodeRuns runs1 := by (try simp at *; expose_names); exact (h1_ensures1); done
  have h2_runs : ∃ runs2 : List (Char × Nat), expandRuns runs2 = input.toList ∧ validRunCounts runs2 ∧ maximalRuns runs2 ∧ runsNoDigits runs2 ∧ ret2.toList = encodeRuns runs2 := by (try simp at *; expose_names); exact (h2_ensures1); done
  -- Key lemma: runs satisfying these properties are unique for a given input
  have runs_unique : ∀ (runs1 runs2 : List (Char × Nat)), expandRuns runs1 = input.toList → expandRuns runs2 = input.toList → validRunCounts runs1 → validRunCounts runs2 → maximalRuns runs1 → maximalRuns runs2 → runs1 = runs2 := by (try simp at *; expose_names); exact (uniqueness_2 input hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h2_ensures1 h1_runs h2_runs); done
  -- From uniqueness of runs, derive that encodeRuns gives the same result
  have encode_eq : ∀ (runs1 runs2 : List (Char × Nat)), runs1 = runs2 → encodeRuns runs1 = encodeRuns runs2 := by (try simp at *; expose_names); exact (fun runs1 runs2 a ↦ congrArg encodeRuns a); done
  -- Get the actual runs from the existential statements
  obtain ⟨runs1, hexp1, hvalid1, hmax1, hnodig1, hret1⟩ := h1_runs
  obtain ⟨runs2, hexp2, hvalid2, hmax2, hnodig2, hret2⟩ := h2_runs
  -- Show that runs1 = runs2
  have runs_eq : runs1 = runs2 := by (try simp at *; expose_names); exact (uniqueness_3 input hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h2_ensures1 runs_unique runs1 hexp1 hvalid1 hmax1 hnodig1 hret1 runs2 hexp2 hvalid2 hmax2 hnodig2 hret2 encode_eq); done
  -- Show that the encoded results are equal
  have enc_eq : encodeRuns runs1 = encodeRuns runs2 := by (try simp at *; expose_names); exact (congrArg encodeRuns runs_eq); done
  -- Show that ret1.toList = ret2.toList
  have toList_eq : ret1.toList = ret2.toList := by (try simp at *; expose_names); exact (uniqueness_4 input hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h2_ensures1 runs_unique runs1 hexp1 hvalid1 hmax1 hnodig1 hret1 runs2 hexp2 hvalid2 hmax2 hnodig2 hret2 runs_eq enc_eq encode_eq); done
  -- Use String.ext_iff to conclude ret1 = ret2
  have string_ext : ret1 = ret2 ↔ ret1.toList = ret2.toList := by (try simp at *; expose_names); exact (String.ext_iff); done
  exact string_ext.mpr toList_eq
end Proof
