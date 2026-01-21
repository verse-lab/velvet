import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def isSortedArray (arr : Array Nat) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size → arr[i]! ≤ arr[j]!

def countInArray (arr : Array Nat) (v : Nat) : Nat :=
  arr.toList.count v



def precondition (a1 : Array Nat) (a2 : Array Nat) : Prop :=
  isSortedArray a1 ∧ isSortedArray a2



def ensures1 (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  result.size = a1.size + a2.size


def ensures2 (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  isSortedArray result


def ensures3 (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  ∀ v : Nat, countInArray result v = countInArray a1 v + countInArray a2 v

def postcondition (a1 : Array Nat) (a2 : Array Nat) (result : Array Nat) : Prop :=
  ensures1 a1 a2 result ∧
  ensures2 a1 a2 result ∧
  ensures3 a1 a2 result


def test1_a1 : Array Nat := #[1, 3, 5]

def test1_a2 : Array Nat := #[2, 4, 6]

def test1_Expected : Array Nat := #[1, 2, 3, 4, 5, 6]

def test5_a1 : Array Nat := #[1, 1, 2]

def test5_a2 : Array Nat := #[1, 2, 2]

def test5_Expected : Array Nat := #[1, 1, 1, 2, 2, 2]

def test6_a1 : Array Nat := #[10, 20, 30]

def test6_a2 : Array Nat := #[5, 15, 25]

def test6_Expected : Array Nat := #[5, 10, 15, 20, 25, 30]







section Proof
theorem test1_precondition :
  precondition test1_a1 test1_a2 := by
  unfold precondition isSortedArray test1_a1 test1_a2
  constructor
  · intro i j hij hj
    simp only [Array.size_toArray, List.length_cons, List.length_nil] at hj
    have hi : i < 3 := Nat.lt_trans hij hj
    match i, j with
    | 0, 0 => omega
    | 0, 1 => decide
    | 0, 2 => decide
    | 1, 0 => omega
    | 1, 1 => omega
    | 1, 2 => decide
    | 2, _ => omega
    | i + 3, _ => omega
  · intro i j hij hj
    simp only [Array.size_toArray, List.length_cons, List.length_nil] at hj
    match i, j with
    | 0, 0 => omega
    | 0, 1 => decide
    | 0, 2 => decide
    | 1, 0 => omega
    | 1, 1 => omega
    | 1, 2 => decide
    | 2, _ => omega
    | i + 3, _ => omega

theorem test1_postcondition_0
    (v : ℕ)
    (h_list_result : True)
    (h_list_a1 : True)
    (h_list_a2 : True)
    : ∀ (w : ℕ), List.count w [1, 2, 3, 4, 5, 6] = if w = 1 then 1 else if w = 2 then 1 else if w = 3 then 1 else if w = 4 then 1 else if w = 5 then 1 else if w = 6 then 1 else 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_1
    (v : ℕ)
    (h_count_result : ∀ (w : ℕ), List.count w [1, 2, 3, 4, 5, 6] = if w = 1 then 1 else if w = 2 then 1 else if w = 3 then 1 else if w = 4 then 1 else if w = 5 then 1 else if w = 6 then 1 else 0)
    (h_list_result : True)
    (h_list_a1 : True)
    (h_list_a2 : True)
    : ∀ (w : ℕ), List.count w [1, 3, 5] = if w = 1 then 1 else if w = 3 then 1 else if w = 5 then 1 else 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_2
    (v : ℕ)
    (h_count_result : ∀ (w : ℕ), List.count w [1, 2, 3, 4, 5, 6] = if w = 1 then 1 else if w = 2 then 1 else if w = 3 then 1 else if w = 4 then 1 else if w = 5 then 1 else if w = 6 then 1 else 0)
    (h_count_a1 : ∀ (w : ℕ), List.count w [1, 3, 5] = if w = 1 then 1 else if w = 3 then 1 else if w = 5 then 1 else 0)
    (h_list_result : True)
    (h_list_a1 : True)
    (h_list_a2 : True)
    : ∀ (w : ℕ), List.count w [2, 4, 6] = if w = 2 then 1 else if w = 4 then 1 else if w = 6 then 1 else 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition_3
    (v : ℕ)
    (h_count_result : ∀ (w : ℕ), List.count w [1, 2, 3, 4, 5, 6] = if w = 1 then 1 else if w = 2 then 1 else if w = 3 then 1 else if w = 4 then 1 else if w = 5 then 1 else if w = 6 then 1 else 0)
    (h_count_a1 : ∀ (w : ℕ), List.count w [1, 3, 5] = if w = 1 then 1 else if w = 3 then 1 else if w = 5 then 1 else 0)
    (h_count_a2 : ∀ (w : ℕ), List.count w [2, 4, 6] = if w = 2 then 1 else if w = 4 then 1 else if w = 6 then 1 else 0)
    (h_list_result : True)
    (h_list_a1 : True)
    (h_list_a2 : True)
    : List.count v [1, 2, 3, 4, 5, 6] = List.count v [1, 3, 5] + List.count v [2, 4, 6] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test1_postcondition :
  postcondition test1_a1 test1_a2 test1_Expected := by
  unfold postcondition
  constructor
  · -- ensures1: result.size = a1.size + a2.size
    have h_ensures1 : ensures1 test1_a1 test1_a2 test1_Expected := by
      unfold ensures1 test1_a1 test1_a2 test1_Expected
      native_decide
    exact h_ensures1
  constructor
  · -- ensures2: result is sorted
    have h_ensures2 : ensures2 test1_a1 test1_a2 test1_Expected := by
      unfold ensures2 isSortedArray test1_Expected
      intro i j hij hj
      simp only [Array.size_toArray, List.length_cons, List.length_nil] at hj
      have hi : i < 6 := Nat.lt_trans hij hj
      match i, j with
      | 0, 0 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 0, 1 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 0, 2 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 0, 3 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 0, 4 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 0, 5 => (try simp at *; expose_names); exact hi; done
      | 1, 0 => (try simp at *; expose_names); exact Nat.le_succ_of_le hij; done
      | 1, 1 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 1, 2 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 1, 3 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 1, 4 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 1, 5 => (try simp at *; expose_names); exact hi; done
      | 2, 0 => (try simp at *; expose_names); exact Nat.le_succ_of_le hij; done
      | 2, 1 => (try simp at *; expose_names); exact Nat.le_succ_of_le hij; done
      | 2, 2 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 2, 3 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 2, 4 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 2, 5 => (try simp at *; expose_names); exact hi; done
      | 3, 0 => (try simp at *; expose_names); exact Nat.le_succ_of_le hij; done
      | 3, 1 => (try simp at *; expose_names); exact Nat.le_succ_of_le hij; done
      | 3, 2 => (try simp at *; expose_names); exact Nat.le_succ_of_le hij; done
      | 3, 3 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 3, 4 => (try simp at *; expose_names); exact Nat.le_of_lt_succ hj; done
      | 3, 5 => (try simp at *; expose_names); exact hi; done
      | 4, 0 => (try simp at *; expose_names); exact Nat.le_succ_of_le hij; done
      | 4, 1 => (try simp at *; expose_names); exact Nat.le_succ_of_le hij; done
      | 4, 2 => (try simp at *; expose_names); exact Nat.le_succ_of_le hij; done
      | 4, 3 => (try simp at *; expose_names); exact Nat.le_succ_of_le hij; done
      | 4, 4 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 4, 5 => (try simp at *; expose_names); exact hi; done
      | 5, _ => (try simp at *; expose_names); exact le_imp_le_of_lt_imp_lt (fun a ↦ hj) hij; done
      | i + 6, _ => (try simp at *; expose_names); (expose_names; (exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a ↦ a) rfl #[1, 2, 3, 4, 5, 6][x]!)); done
    exact h_ensures2
  · -- ensures3: count preservation
    have h_ensures3 : ensures3 test1_a1 test1_a2 test1_Expected := by
      unfold ensures3 countInArray test1_a1 test1_a2 test1_Expected
      intro v
      have h_list_result : #[1, 2, 3, 4, 5, 6].toList = [1, 2, 3, 4, 5, 6] := by (try simp at *; expose_names); exact (rfl); done
      have h_list_a1 : #[1, 3, 5].toList = [1, 3, 5] := by (try simp at *; expose_names); exact (rfl); done
      have h_list_a2 : #[2, 4, 6].toList = [2, 4, 6] := by (try simp at *; expose_names); exact (rfl); done
      have h_count_result : ∀ w, List.count w [1, 2, 3, 4, 5, 6] = if w = 1 then 1 else if w = 2 then 1 else if w = 3 then 1 else if w = 4 then 1 else if w = 5 then 1 else if w = 6 then 1 else 0 := by (try simp at *; expose_names); exact (test1_postcondition_0 v h_list_result h_list_a1 h_list_a2); done
      have h_count_a1 : ∀ w, List.count w [1, 3, 5] = if w = 1 then 1 else if w = 3 then 1 else if w = 5 then 1 else 0 := by (try simp at *; expose_names); exact (test1_postcondition_1 v h_count_result h_list_result h_list_a1 h_list_a2); done
      have h_count_a2 : ∀ w, List.count w [2, 4, 6] = if w = 2 then 1 else if w = 4 then 1 else if w = 6 then 1 else 0 := by (try simp at *; expose_names); exact (test1_postcondition_2 v h_count_result h_count_a1 h_list_result h_list_a1 h_list_a2); done
      have h_main : List.count v [1, 2, 3, 4, 5, 6] = List.count v [1, 3, 5] + List.count v [2, 4, 6] := by (try simp at *; expose_names); exact (test1_postcondition_3 v h_count_result h_count_a1 h_count_a2 h_list_result h_list_a1 h_list_a2); done
      simp only [h_list_result, h_list_a1, h_list_a2]
      exact h_main
    exact h_ensures3

theorem test5_precondition :
  precondition test5_a1 test5_a2 := by
  unfold precondition isSortedArray test5_a1 test5_a2
  constructor
  · -- Prove isSortedArray #[1, 1, 2]
    intro i j hij hj
    simp only [Array.size_toArray, List.length_cons, List.length_nil] at hj
    have hi : i < 3 := Nat.lt_trans hij hj
    match i, j with
    | 0, 0 => omega
    | 0, 1 => decide
    | 0, 2 => decide
    | 1, 0 => omega
    | 1, 1 => omega
    | 1, 2 => decide
    | 2, _ => omega
    | i + 3, _ => omega
  · -- Prove isSortedArray #[1, 2, 2]
    intro i j hij hj
    simp only [Array.size_toArray, List.length_cons, List.length_nil] at hj
    match i, j with
    | 0, 0 => omega
    | 0, 1 => decide
    | 0, 2 => decide
    | 1, 0 => omega
    | 1, 1 => omega
    | 1, 2 => decide
    | 2, _ => omega
    | i + 3, _ => omega

theorem test5_postcondition_0
    (i : ℕ)
    (j : ℕ)
    (hij : 3 < 0)
    (hj : 0 < 0 + 1 + 1 + 1 + 1 + 1 + 1)
    (hi : 3 < 6)
    : #[1, 1, 1, 2, 2, 2][3]! ≤ #[1, 1, 1, 2, 2, 2][0]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test5_postcondition_1
    (i : ℕ)
    (j : ℕ)
    (hij : 3 < 2)
    (hj : 2 < 0 + 1 + 1 + 1 + 1 + 1 + 1)
    (hi : 3 < 6)
    : #[1, 1, 1, 2, 2, 2][3]! ≤ #[1, 1, 1, 2, 2, 2][2]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test5_postcondition_2
    (i : ℕ)
    (j : ℕ)
    (hij : 4 < 0)
    (hj : 0 < 0 + 1 + 1 + 1 + 1 + 1 + 1)
    (hi : 4 < 6)
    : #[1, 1, 1, 2, 2, 2][4]! ≤ #[1, 1, 1, 2, 2, 2][0]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test5_postcondition_3
    (i : ℕ)
    (j : ℕ)
    (hij : 4 < 2)
    (hj : 2 < 0 + 1 + 1 + 1 + 1 + 1 + 1)
    (hi : 4 < 6)
    : #[1, 1, 1, 2, 2, 2][4]! ≤ #[1, 1, 1, 2, 2, 2][2]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test5_postcondition_4
    (v : ℕ)
    (h_list_result : True)
    (h_list_a1 : True)
    (h_list_a2 : True)
    : ∀ (w : ℕ), List.count w [1, 1, 1, 2, 2, 2] = if w = 1 then 3 else if w = 2 then 3 else 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test5_postcondition_5
    (v : ℕ)
    (h_count_result : ∀ (w : ℕ), List.count w [1, 1, 1, 2, 2, 2] = if w = 1 then 3 else if w = 2 then 3 else 0)
    (h_list_result : True)
    (h_list_a1 : True)
    (h_list_a2 : True)
    : ∀ (w : ℕ), List.count w [1, 1, 2] = if w = 1 then 2 else if w = 2 then 1 else 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test5_postcondition_6
    (v : ℕ)
    (h_count_result : ∀ (w : ℕ), List.count w [1, 1, 1, 2, 2, 2] = if w = 1 then 3 else if w = 2 then 3 else 0)
    (h_count_a1 : ∀ (w : ℕ), List.count w [1, 1, 2] = if w = 1 then 2 else if w = 2 then 1 else 0)
    (h_list_result : True)
    (h_list_a1 : True)
    (h_list_a2 : True)
    : ∀ (w : ℕ), List.count w [1, 2, 2] = if w = 1 then 1 else if w = 2 then 2 else 0 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test5_postcondition_7
    (v : ℕ)
    (h_count_result : ∀ (w : ℕ), List.count w [1, 1, 1, 2, 2, 2] = if w = 1 then 3 else if w = 2 then 3 else 0)
    (h_count_a1 : ∀ (w : ℕ), List.count w [1, 1, 2] = if w = 1 then 2 else if w = 2 then 1 else 0)
    (h_count_a2 : ∀ (w : ℕ), List.count w [1, 2, 2] = if w = 1 then 1 else if w = 2 then 2 else 0)
    (h_list_result : True)
    (h_list_a1 : True)
    (h_list_a2 : True)
    : List.count v [1, 1, 1, 2, 2, 2] = List.count v [1, 1, 2] + List.count v [1, 2, 2] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem test5_postcondition :
  postcondition test5_a1 test5_a2 test5_Expected := by
  unfold postcondition
  constructor
  · -- ensures1: result.size = a1.size + a2.size (6 = 3 + 3)
    have h_ensures1 : ensures1 test5_a1 test5_a2 test5_Expected := by
      unfold ensures1 test5_a1 test5_a2 test5_Expected
      native_decide
    exact h_ensures1
  constructor
  · -- ensures2: result is sorted
    have h_ensures2 : ensures2 test5_a1 test5_a2 test5_Expected := by
      unfold ensures2 isSortedArray test5_Expected
      intro i j hij hj
      simp only [Array.size_toArray, List.length_cons, List.length_nil] at hj
      have hi : i < 6 := Nat.lt_trans hij hj
      match i, j with
      | 0, 0 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 0, 1 => (try simp at *; expose_names); exact hij; done
      | 0, 2 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 0, 3 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 0, 4 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 0, 5 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 1, 0 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 1, 1 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 1, 2 => (try simp at *; expose_names); exact Nat.le_of_lt_succ hij; done
      | 1, 3 => (try simp at *; expose_names); exact Nat.le_of_lt_succ hij; done
      | 1, 4 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 1, 5 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 2, 0 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 2, 1 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 2, 2 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 2, 3 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 2, 4 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 2, 5 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 3, 0 => (try simp at *; expose_names); exact (test5_postcondition_0 i j hij hj hi); done
      | 3, 1 => (try simp at *; expose_names); exact Nat.le_of_add_left_le hij; done
      | 3, 2 => (try simp at *; expose_names); exact (test5_postcondition_1 i j hij hj hi); done
      | 3, 3 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 3, 4 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 3, 5 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 4, 0 => (try simp at *; expose_names); exact (test5_postcondition_2 i j hij hj hi); done
      | 4, 1 => (try simp at *; expose_names); exact Nat.le_of_add_left_le hij; done
      | 4, 2 => (try simp at *; expose_names); exact (test5_postcondition_3 i j hij hj hi); done
      | 4, 3 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 4, 4 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 4, 5 => (try simp at *; expose_names); exact Nat.le_of_ble_eq_true rfl; done
      | 5, _ => (try simp at *; expose_names); exact le_imp_le_of_lt_imp_lt (fun a ↦ hj) hij; done
      | i + 6, _ => (try simp at *; expose_names); (expose_names; (exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a ↦ a) rfl #[1, 1, 1, 2, 2, 2][x]!)); done
    exact h_ensures2
  · -- ensures3: count preservation
    have h_ensures3 : ensures3 test5_a1 test5_a2 test5_Expected := by
      unfold ensures3 countInArray test5_a1 test5_a2 test5_Expected
      intro v
      have h_list_result : #[1, 1, 1, 2, 2, 2].toList = [1, 1, 1, 2, 2, 2] := by (try simp at *; expose_names); exact (rfl); done
      have h_list_a1 : #[1, 1, 2].toList = [1, 1, 2] := by (try simp at *; expose_names); exact (rfl); done
      have h_list_a2 : #[1, 2, 2].toList = [1, 2, 2] := by (try simp at *; expose_names); exact (rfl); done
      have h_count_result : ∀ w, List.count w [1, 1, 1, 2, 2, 2] = if w = 1 then 3 else if w = 2 then 3 else 0 := by (try simp at *; expose_names); exact (test5_postcondition_4 v h_list_result h_list_a1 h_list_a2); done
      have h_count_a1 : ∀ w, List.count w [1, 1, 2] = if w = 1 then 2 else if w = 2 then 1 else 0 := by (try simp at *; expose_names); exact (test5_postcondition_5 v h_count_result h_list_result h_list_a1 h_list_a2); done
      have h_count_a2 : ∀ w, List.count w [1, 2, 2] = if w = 1 then 1 else if w = 2 then 2 else 0 := by (try simp at *; expose_names); exact (test5_postcondition_6 v h_count_result h_count_a1 h_list_result h_list_a1 h_list_a2); done
      have h_main : List.count v [1, 1, 1, 2, 2, 2] = List.count v [1, 1, 2] + List.count v [1, 2, 2] := by (try simp at *; expose_names); exact (test5_postcondition_7 v h_count_result h_count_a1 h_count_a2 h_list_result h_list_a1 h_list_a2); done
      simp only [h_list_result, h_list_a1, h_list_a2]
      exact h_main
    exact h_ensures3

theorem test6_precondition :
  precondition test6_a1 test6_a2 := by
  unfold precondition isSortedArray test6_a1 test6_a2
  constructor
  · intro i j hij hj
    simp only [Array.size_toArray, List.length_cons, List.length_nil] at hj
    match i, j with
    | 0, 0 => omega
    | 0, 1 => decide
    | 0, 2 => decide
    | 1, 0 => omega
    | 1, 1 => omega
    | 1, 2 => decide
    | 2, 0 => omega
    | 2, 1 => omega
    | 2, 2 => omega
    | _, j + 3 => omega
    | i + 3, _ => omega
  · intro i j hij hj
    simp only [Array.size_toArray, List.length_cons, List.length_nil] at hj
    match i, j with
    | 0, 0 => omega
    | 0, 1 => decide
    | 0, 2 => decide
    | 1, 0 => omega
    | 1, 1 => omega
    | 1, 2 => decide
    | 2, 0 => omega
    | 2, 1 => omega
    | 2, 2 => omega
    | _, j + 3 => omega
    | i + 3, _ => omega

theorem test6_postcondition_0 : ensures2 test6_a1 test6_a2 test6_Expected := by
  unfold ensures2 isSortedArray test6_Expected
  intro i j hij hj
  have hi : i < 6 := Nat.lt_trans hij hj
  simp only [Array.size_toArray, List.length_cons, List.length_nil] at hj
  interval_cases i <;> interval_cases j <;> simp_all

theorem test6_postcondition_1 : ensures3 test6_a1 test6_a2 test6_Expected := by
  unfold ensures3 countInArray test6_a1 test6_a2 test6_Expected
  intro v
  simp only [List.count_cons, List.count_nil]
  by_cases h5 : 5 = v <;> by_cases h10 : 10 = v <;> by_cases h15 : 15 = v <;> 
  by_cases h20 : 20 = v <;> by_cases h25 : 25 = v <;> by_cases h30 : 30 = v <;>
  simp_all <;> omega

theorem test6_postcondition :
  postcondition test6_a1 test6_a2 test6_Expected := by
  unfold postcondition
  constructor
  · -- ensures1: result.size = a1.size + a2.size (6 = 3 + 3)
    have h_ensures1 : ensures1 test6_a1 test6_a2 test6_Expected := by (try simp at *; expose_names); exact (rfl); done
    exact h_ensures1
  constructor
  · -- ensures2: result is sorted
    have h_ensures2 : ensures2 test6_a1 test6_a2 test6_Expected := by (try simp at *; expose_names); exact (test6_postcondition_0); done
    exact h_ensures2
  · -- ensures3: count preservation
    have h_ensures3 : ensures3 test6_a1 test6_a2 test6_Expected := by (try simp at *; expose_names); exact (test6_postcondition_1); done
    exact h_ensures3

theorem uniqueness_0
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (hpre : precondition a1 a2)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition a1 a2 ret1)
    (hpost2 : postcondition a1 a2 ret2)
    : ensures1 a1 a2 ret1 := by
    exact hpost1.1

theorem uniqueness_1
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (hpre : precondition a1 a2)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition a1 a2 ret1)
    (hpost2 : postcondition a1 a2 ret2)
    (h1_ensures1 : ensures1 a1 a2 ret1)
    : ensures2 a1 a2 ret1 := by
    exact hpost1.2.1

theorem uniqueness_2
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (hpre : precondition a1 a2)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition a1 a2 ret1)
    (hpost2 : postcondition a1 a2 ret2)
    (h1_ensures1 : ensures1 a1 a2 ret1)
    (h1_ensures2 : ensures2 a1 a2 ret1)
    : ensures3 a1 a2 ret1 := by
    exact hpost1.2.2

theorem uniqueness_3
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (hpre : precondition a1 a2)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition a1 a2 ret1)
    (hpost2 : postcondition a1 a2 ret2)
    (h1_ensures1 : ensures1 a1 a2 ret1)
    (h1_ensures2 : ensures2 a1 a2 ret1)
    (h1_ensures3 : ensures3 a1 a2 ret1)
    : ensures1 a1 a2 ret2 := by
    intros; expose_names; exact (uniqueness_0 a1 a2 hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_4
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (hpre : precondition a1 a2)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition a1 a2 ret1)
    (hpost2 : postcondition a1 a2 ret2)
    (h1_ensures1 : ensures1 a1 a2 ret1)
    (h1_ensures2 : ensures2 a1 a2 ret1)
    (h1_ensures3 : ensures3 a1 a2 ret1)
    (h2_ensures1 : ensures1 a1 a2 ret2)
    : ensures2 a1 a2 ret2 := by
    intros; expose_names; exact (uniqueness_1 a1 a2 hpre ret2 ret1 hpost2 hpost1 h2_ensures1); done

theorem uniqueness_5
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (hpre : precondition a1 a2)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition a1 a2 ret1)
    (hpost2 : postcondition a1 a2 ret2)
    (h1_ensures1 : ensures1 a1 a2 ret1)
    (h1_ensures2 : ensures2 a1 a2 ret1)
    (h1_ensures3 : ensures3 a1 a2 ret1)
    (h2_ensures1 : ensures1 a1 a2 ret2)
    (h2_ensures2 : ensures2 a1 a2 ret2)
    : ensures3 a1 a2 ret2 := by
    intros; expose_names; exact (uniqueness_2 a1 a2 hpre ret2 ret1 hpost2 hpost1 h2_ensures1 h2_ensures2); done

theorem uniqueness_6
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (hpre : precondition a1 a2)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition a1 a2 ret1)
    (hpost2 : postcondition a1 a2 ret2)
    (h1_ensures1 : ensures1 a1 a2 ret1)
    (h1_ensures2 : ensures2 a1 a2 ret1)
    (h1_ensures3 : ensures3 a1 a2 ret1)
    (h2_ensures1 : ensures1 a1 a2 ret2)
    (h2_ensures2 : ensures2 a1 a2 ret2)
    (h2_ensures3 : ensures3 a1 a2 ret2)
    : ret1.size = ret2.size := by
    unfold ensures1 at h1_ensures1 h2_ensures1
    rw [h1_ensures1, h2_ensures1]

theorem uniqueness_7
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (hpre : precondition a1 a2)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition a1 a2 ret1)
    (hpost2 : postcondition a1 a2 ret2)
    (h1_ensures1 : ensures1 a1 a2 ret1)
    (h1_ensures2 : ensures2 a1 a2 ret1)
    (h1_ensures3 : ensures3 a1 a2 ret1)
    (h2_ensures1 : ensures1 a1 a2 ret2)
    (h2_ensures2 : ensures2 a1 a2 ret2)
    (h2_ensures3 : ensures3 a1 a2 ret2)
    (hsize : ret1.size = ret2.size)
    : ∀ (v : ℕ), Array.count v ret1 = Array.count v ret2 := by
    intro v
    -- h1_ensures3 gives us: countInArray ret1 v = countInArray a1 v + countInArray a2 v
    -- h2_ensures3 gives us: countInArray ret2 v = countInArray a1 v + countInArray a2 v
    -- So countInArray ret1 v = countInArray ret2 v
    unfold ensures3 at h1_ensures3 h2_ensures3
    unfold countInArray at h1_ensures3 h2_ensures3
    -- h1_ensures3 v : ret1.toList.count v = a1.toList.count v + a2.toList.count v
    -- h2_ensures3 v : ret2.toList.count v = a1.toList.count v + a2.toList.count v
    have h1 := h1_ensures3 v
    have h2 := h2_ensures3 v
    -- So ret1.toList.count v = ret2.toList.count v
    have h_eq : ret1.toList.count v = ret2.toList.count v := by omega
    -- Now relate List.count to Array.count using Array.count_toList
    rw [← Array.count_toList, ← Array.count_toList]
    exact h_eq

theorem uniqueness_8
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (hpre : precondition a1 a2)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition a1 a2 ret1)
    (hpost2 : postcondition a1 a2 ret2)
    (h1_ensures1 : ensures1 a1 a2 ret1)
    (h1_ensures2 : ensures2 a1 a2 ret1)
    (h1_ensures3 : ensures3 a1 a2 ret1)
    (h2_ensures1 : ensures1 a1 a2 ret2)
    (h2_ensures2 : ensures2 a1 a2 ret2)
    (h2_ensures3 : ensures3 a1 a2 ret2)
    (hsize : ret1.size = ret2.size)
    (hcount_eq : ∀ (v : ℕ), Array.count v ret1 = Array.count v ret2)
    : ret1.toList.Perm ret2.toList := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_9_0
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (hpre : precondition a1 a2)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition a1 a2 ret1)
    (hpost2 : postcondition a1 a2 ret2)
    (h1_ensures1 : ensures1 a1 a2 ret1)
    (h1_ensures2 : ensures2 a1 a2 ret1)
    (h1_ensures3 : ensures3 a1 a2 ret1)
    (h2_ensures1 : ensures1 a1 a2 ret2)
    (h2_ensures2 : ensures2 a1 a2 ret2)
    (h2_ensures3 : ensures3 a1 a2 ret2)
    (hsize : ret1.size = ret2.size)
    (hperm : ret1.toList.Perm ret2.toList)
    (hcount_eq : ∀ (v : ℕ), Array.count v ret1 = Array.count v ret2)
    (h_sorted_ret1 : isSortedArray ret1)
    (h_length_eq : ret1.toList.length = ret1.size)
    (h_pairwise_iff : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret1.toList ↔ ∀ (i j : ℕ) (hi : i < ret1.size) (hj : j < ret1.size), i < j → ret1[i] ≤ ret1[j])
    (h_getElem_eq : True)
    : ∀ (i j : ℕ) (hi : i < ret1.size) (hj : j < ret1.size), i < j → ret1[i] ≤ ret1[j] := by
    intro i j hi hj hij
    have h := h_sorted_ret1 i j hij hj
    -- h : ret1[i]! ≤ ret1[j]!
    -- Need to show ret1[i] ≤ ret1[j]
    -- When index is in bounds, arr[i]! = arr[i]
    simp only [Array.getElem!_eq_getD, Array.getD_getElem?] at h
    simp only [dif_pos hi, dif_pos hj] at h
    exact h

theorem uniqueness_9
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (hpre : precondition a1 a2)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition a1 a2 ret1)
    (hpost2 : postcondition a1 a2 ret2)
    (h1_ensures1 : ensures1 a1 a2 ret1)
    (h1_ensures2 : ensures2 a1 a2 ret1)
    (h1_ensures3 : ensures3 a1 a2 ret1)
    (h2_ensures1 : ensures1 a1 a2 ret2)
    (h2_ensures2 : ensures2 a1 a2 ret2)
    (h2_ensures3 : ensures3 a1 a2 ret2)
    (hsize : ret1.size = ret2.size)
    (hperm : ret1.toList.Perm ret2.toList)
    (hcount_eq : ∀ (v : ℕ), Array.count v ret1 = Array.count v ret2)
    : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret1.toList := by
    have h_sorted_ret1 : isSortedArray ret1 := by
      (try simp at *; expose_names); exact h1_ensures2; done
    have h_length_eq : ret1.toList.length = ret1.size := by
      (try simp at *; expose_names); exact rfl; done
    have h_pairwise_iff : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret1.toList ↔ 
        ∀ (i j : Nat) (hi : i < ret1.toList.length) (hj : j < ret1.toList.length) (hij : i < j), 
        ret1.toList[i] ≤ ret1.toList[j] := by
      (try simp at *; expose_names); exact List.pairwise_iff_getElem; done
    have h_getElem_eq : ∀ (i : Nat) (h : i < ret1.size), ret1.toList[i]'(by rw [h_length_eq]; exact h) = ret1[i] := by
      (try simp at *; expose_names); exact fun i h ↦ rfl; done
    have h_index_sorted : ∀ (i j : Nat) (hi : i < ret1.toList.length) (hj : j < ret1.toList.length) (hij : i < j), 
        ret1.toList[i] ≤ ret1.toList[j] := by
      (try simp at *; expose_names); exact (uniqueness_9_0 a1 a2 hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h2_ensures1 h2_ensures2 h2_ensures3 hsize hperm hcount_eq h_sorted_ret1 h_length_eq h_pairwise_iff h_getElem_eq); done
    rw [h_pairwise_iff]
    exact h_index_sorted

theorem uniqueness_10
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (hpre : precondition a1 a2)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition a1 a2 ret1)
    (hpost2 : postcondition a1 a2 ret2)
    (h1_ensures1 : ensures1 a1 a2 ret1)
    (h1_ensures2 : ensures2 a1 a2 ret1)
    (h1_ensures3 : ensures3 a1 a2 ret1)
    (h2_ensures1 : ensures1 a1 a2 ret2)
    (h2_ensures2 : ensures2 a1 a2 ret2)
    (h2_ensures3 : ensures3 a1 a2 ret2)
    (hsize : ret1.size = ret2.size)
    (hperm : ret1.toList.Perm ret2.toList)
    (hsorted1 : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret1.toList)
    (hcount_eq : ∀ (v : ℕ), Array.count v ret1 = Array.count v ret2)
    : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret2.toList := by
    unfold ensures2 isSortedArray at h2_ensures2
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hi' : i < ret2.size := by simp [Array.length_toList] at hi; exact hi
    have hj' : j < ret2.size := by simp [Array.length_toList] at hj; exact hj
    rw [Array.getElem_toList hi', Array.getElem_toList hj']
    have h := h2_ensures2 i j hij hj'
    -- h : ret2[i]! ≤ ret2[j]!
    -- We need: ret2[i] ≤ ret2[j]
    -- When i < ret2.size, ret2[i]! = ret2[i]
    have eq_i : ret2[i]! = ret2[i] := by
      simp only [Array.getElem!_eq_getD]
      unfold Array.getD
      simp [hi']
    have eq_j : ret2[j]! = ret2[j] := by
      simp only [Array.getElem!_eq_getD]
      unfold Array.getD
      simp [hj']
    rw [eq_i, eq_j] at h
    exact h

theorem uniqueness_11
    (a1 : Array ℕ)
    (a2 : Array ℕ)
    (hpre : precondition a1 a2)
    (ret1 : Array ℕ)
    (ret2 : Array ℕ)
    (hpost1 : postcondition a1 a2 ret1)
    (hpost2 : postcondition a1 a2 ret2)
    (h1_ensures1 : ensures1 a1 a2 ret1)
    (h1_ensures2 : ensures2 a1 a2 ret1)
    (h1_ensures3 : ensures3 a1 a2 ret1)
    (h2_ensures1 : ensures1 a1 a2 ret2)
    (h2_ensures2 : ensures2 a1 a2 ret2)
    (h2_ensures3 : ensures3 a1 a2 ret2)
    (hsize : ret1.size = ret2.size)
    (hperm : ret1.toList.Perm ret2.toList)
    (hsorted1 : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret1.toList)
    (hsorted2 : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ret2.toList)
    (hcount_eq : ∀ (v : ℕ), Array.count v ret1 = Array.count v ret2)
    (hantisym : ∀ (a b : ℕ), a ∈ ret1 → b ∈ ret2 → a ≤ b → b ≤ a → a = b)
    : ret1 = ret2 := by
  apply Array.ext'
  apply List.Perm.eq_of_sorted _ hsorted1 hsorted2 hperm
  intro a b ha hb hab hba
  have ha' : a ∈ ret1 := by
    rw [Array.mem_def]
    exact ha
  have hb' : b ∈ ret2 := by
    rw [Array.mem_def]
    exact hb
  exact hantisym a b ha' hb' hab hba

theorem uniqueness (a1 : Array Nat) (a2 : Array Nat):
  precondition a1 a2 →
  (∀ ret1 ret2,
    postcondition a1 a2 ret1 →
    postcondition a1 a2 ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  -- Extract the three ensures conditions from both postconditions
  have h1_ensures1 : ensures1 a1 a2 ret1 := by (try simp at *; expose_names); exact (uniqueness_0 a1 a2 hpre ret1 ret2 hpost1 hpost2); done
  have h1_ensures2 : ensures2 a1 a2 ret1 := by (try simp at *; expose_names); exact (uniqueness_1 a1 a2 hpre ret1 ret2 hpost1 hpost2 h1_ensures1); done
  have h1_ensures3 : ensures3 a1 a2 ret1 := by (try simp at *; expose_names); exact (uniqueness_2 a1 a2 hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2); done
  have h2_ensures1 : ensures1 a1 a2 ret2 := by (try simp at *; expose_names); exact (uniqueness_3 a1 a2 hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3); done
  have h2_ensures2 : ensures2 a1 a2 ret2 := by (try simp at *; expose_names); exact (uniqueness_4 a1 a2 hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h2_ensures1); done
  have h2_ensures3 : ensures3 a1 a2 ret2 := by (try simp at *; expose_names); exact (uniqueness_5 a1 a2 hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h2_ensures1 h2_ensures2); done
  -- Both results have the same size
  have hsize : ret1.size = ret2.size := by (try simp at *; expose_names); exact (uniqueness_6 a1 a2 hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h2_ensures1 h2_ensures2 h2_ensures3); done
  -- Both lists have the same count for every element
  have hcount_eq : ∀ v : Nat, ret1.toList.count v = ret2.toList.count v := by (try simp at *; expose_names); exact (uniqueness_7 a1 a2 hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h2_ensures1 h2_ensures2 h2_ensures3 hsize); done
  -- Two lists with same counts are permutations of each other
  have hperm : ret1.toList.Perm ret2.toList := by (try simp at *; expose_names); exact (uniqueness_8 a1 a2 hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h2_ensures1 h2_ensures2 h2_ensures3 hsize hcount_eq); done
  -- ret1.toList is sorted (as a pairwise relation)
  have hsorted1 : ret1.toList.Pairwise (· ≤ ·) := by (try simp at *; expose_names); exact (uniqueness_9 a1 a2 hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h2_ensures1 h2_ensures2 h2_ensures3 hsize hperm hcount_eq); done
  -- ret2.toList is sorted (as a pairwise relation)
  have hsorted2 : ret2.toList.Pairwise (· ≤ ·) := by (try simp at *; expose_names); exact (uniqueness_10 a1 a2 hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h2_ensures1 h2_ensures2 h2_ensures3 hsize hperm hsorted1 hcount_eq); done
  -- Two sorted permutations are equal (need antisymmetry condition for Nat.le)
  have hantisym : ∀ a b : Nat, a ∈ ret1.toList → b ∈ ret2.toList → a ≤ b → b ≤ a → a = b := by (try simp at *; expose_names); exact (fun a b a_1 a_2 a_3 a_4 ↦ Nat.le_antisymm a_3 a_4); done
  -- The two lists are equal
  have hlist_eq : ret1.toList = ret2.toList := by (try simp at *; expose_names); exact (uniqueness_11 a1 a2 hpre ret1 ret2 hpost1 hpost2 h1_ensures1 h1_ensures2 h1_ensures3 h2_ensures1 h2_ensures2 h2_ensures3 hsize hperm hsorted1 hsorted2 hcount_eq hantisym); done
  -- Array equality from list equality
  exact Array.ext' hlist_eq
end Proof
