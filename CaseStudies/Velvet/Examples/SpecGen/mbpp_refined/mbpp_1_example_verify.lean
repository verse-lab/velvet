import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000

-- Helper Functions

def isValidPath (path: List (Nat × Nat)) (startRow startCol endRow endCol: Nat) : Prop :=
  path.length > 0 ∧
  path.head? = some (startRow, startCol) ∧
  path.getLast? = some (endRow, endCol) ∧
  ∀ i, i + 1 < path.length →
    let curr := path[i]!
    let next := path[i + 1]!
    (next.1 = curr.1 ∧ next.2 = curr.2 + 1) ∨      -- right move
    (next.1 = curr.1 + 1 ∧ next.2 = curr.2) ∨      -- down move
    (next.1 = curr.1 + 1 ∧ next.2 = curr.2 + 1)    -- diagonal down-right move

def pathCost (cost: Array (Array Nat)) (path: List (Nat × Nat)) : Nat :=
  path.foldl (fun acc (i, j) =>
    acc + (cost[i]!)[j]!) 0

def require1 (cost: Array (Array Nat)) (m: Nat) (n: Nat) :=
  cost.size > 0
def require2 (cost: Array (Array Nat)) (m: Nat) (n: Nat) :=
  ∀ i < cost.size, cost[i]!.size > 0
def require3 (cost: Array (Array Nat)) (m: Nat) (n: Nat) :=
  ∀ i < cost.size, cost[i]!.size = cost[0]!.size
def require4 (cost: Array (Array Nat)) (m: Nat) (n: Nat) :=
  m < cost.size
def require5 (cost: Array (Array Nat)) (m: Nat) (n: Nat) :=
  n < cost[0]!.size

def ensures1 (cost: Array (Array Nat)) (m: Nat) (n: Nat) (minCost: Nat) :=
  ∃ path, isValidPath path 0 0 m n ∧ pathCost cost path = minCost  -- achievable minimum
def ensures2 (cost: Array (Array Nat)) (m: Nat) (n: Nat) (minCost: Nat) :=
  ∀ path, isValidPath path 0 0 m n → pathCost cost path ≥ minCost  -- truly minimum
def ensures3 (cost: Array (Array Nat)) (m: Nat) (n: Nat) (minCost: Nat) :=
  (m = 0 ∧ n = 0) → minCost = (cost[0]!)[0]!  -- edge case: start equals end

def precondition (cost: Array (Array Nat)) (m: Nat) (n: Nat) :=
  require1 cost m n ∧ require2 cost m n ∧ require3 cost m n ∧ require4 cost m n ∧ require5 cost m n

def postcondition (cost: Array (Array Nat)) (m: Nat) (n: Nat) (minCost: Nat) :=
  ensures1 cost m n minCost ∧ ensures2 cost m n minCost ∧ ensures3 cost m n minCost

-- Test Cases
def test1_cost : Array (Array Nat) := #[#[1, 2, 3], #[4, 8, 2], #[1, 5, 3]]

def test1_m : Nat := 2

def test1_n : Nat := 2

def test1_Expected : Nat := 8

def test2_cost : Array (Array Nat) := #[#[5]]

def test2_m : Nat := 0

def test2_n : Nat := 0

def test2_Expected : Nat := 5

def test3_cost : Array (Array Nat) := #[#[1, 10], #[10, 1]]

def test3_m : Nat := 1

def test3_n : Nat := 1

def test3_Expected : Nat := 2

def test4_cost : Array (Array Nat) := #[#[1, 5, 5], #[5, 1, 5], #[5, 5, 1]]

def test4_m : Nat := 2

def test4_n : Nat := 2

def test4_Expected : Nat := 3

def test7_cost : Array (Array Nat) := #[#[1, 1, 1], #[1, 1, 1], #[1, 1, 1]]

def test7_m : Nat := 2

def test7_n : Nat := 2

def test7_Expected : Nat := 3

def test12_cost : Array (Array Nat) := #[#[1, 1, 1], #[1, 100, 1], #[1, 1, 1]]

def test12_m : Nat := 2

def test12_n : Nat := 2

def test12_Expected : Nat := 4

-------------------------------
-- Verifications
-------------------------------

-- test1
lemma test1_precondition :
  precondition test1_cost test1_m test1_n := by
  -- Verify that the cost matrix is non-empty and rectangular.
  simp [precondition, test1_cost, test1_m, test1_n];
  -- Verify that the cost matrix is non-empty and rectangular for test1.
  simp [require1, require2, require3, require4, require5];
  native_decide

lemma test1_postcondition :
  postcondition test1_cost test1_m test1_n test1_Expected := by
  -- Let's verify the postcondition for test1.
  apply And.intro; exact (by
  -- Let's construct the path explicitly.
  use [(0, 0), (0, 1), (1, 2), (2, 2)];
  simp +decide [ isValidPath ];
  -- Let's verify each step of the path.
  intro i hi
  interval_cases _ : i + 1 <;> simp_all +decide [ List.get ]); apply And.intro; exact (by
  intro path hpath
  obtain ⟨hstart, hend, hvalid⟩ := hpath;
  -- Let's unfold the definition of `pathCost` to use the properties of the cost matrix.
  simp [pathCost] at *;
  -- By definition of `path`, we know that it must pass through the cells (0,0), (1,1), and (2,2).
  have h_path : ∀ i < path.length, (path[i]!.1 ≤ 2 ∧ path[i]!.2 ≤ 2) := by
    -- By definition of `path`, we know that it must pass through the cells (0,0), (1,1), and (2,2) because of the movement constraints.
    have h_path : ∀ i < path.length, (path[i]!.1 ≤ 2 ∧ path[i]!.2 ≤ 2) := by
      intro i hi
      have h_last : path.getLast! = (2, 2) := by
        aesop
      have h_path : ∀ j, i ≤ j → j < path.length → (path[j]!.1 ≥ path[i]!.1 ∧ path[j]!.2 ≥ path[i]!.2) := by
        -- By induction on $j - i$, we can show that the coordinates at $j$ are at least as large as those at $i$.
        intros j hij hj
        induction' hij with j hj ih;
        · norm_num;
        · specialize ih ( Nat.lt_of_succ_lt hj ) ; specialize hvalid ; aesop;
          · grind;
          · specialize right_2 j hj ; aesop ; omega;
            linarith;
      bound;
      · specialize h_path ( List.length path - 1 ) ( Nat.le_sub_one_of_lt hi ) ( Nat.sub_lt hstart zero_lt_one ) ; aesop;
        rw [ List.getLast?_eq_getElem? ] at left ; aesop;
      · have := h_path ( List.length path - 1 ) ( Nat.le_sub_one_of_lt hi ) ( Nat.sub_lt hstart zero_lt_one ) ; aesop;
        grind +ring;
    assumption;
  -- Let's unfold the definition of `path` to use the properties of the cost matrix.
  have h_path_length : path.length ≤ 5 := by
    have h_path_length : ∀ i < path.length, (path[i]!.1 + path[i]!.2) ≥ i := by
      intro i hi; induction' i with i ih <;> aesop;
      grind;
    grind +ring;
  rcases path with ( _ | ⟨ ⟨ x, y ⟩, _ | ⟨ ⟨ z, w ⟩, _ | ⟨ ⟨ u, v ⟩, _ | ⟨ ⟨ t, s ⟩, _ | ⟨ ⟨ r, q ⟩, _ | path ⟩ ⟩ ⟩ ⟩ ⟩ ) <;> simp +arith +decide at *;
  · -- Since $x = 0$ and $y = 0$, but $x = test1_m$ and $y = test1_n$, we have a contradiction.
    aesop;
    contradiction;
  · aesop ( simp_config := { decide := true } ) ;
  · have := hvalid.2 0; have := hvalid.2 1; simp_all +arith +decide;
    unfold test1_m test1_n test1_Expected test1_cost; aesop;
    · cases left;
    · contradiction;
    · contradiction;
  · have := hvalid.2 0; have := hvalid.2 1; have := hvalid.2 2; norm_num at * ; aesop ( simp_config := { decide := true } ) ;
  · have := hvalid.2 0; have := hvalid.2 1; have := hvalid.2 2; have := hvalid.2 3; simp_all +arith +decide;
    rcases this with ( ⟨ ht, hs ⟩ | ⟨ ht, hs ⟩ | ⟨ ht, hs ⟩ ) <;> simp_all +arith +decide only [test1_m,
                                                                          test1_n];
    · subst ht; norm_num [ test1_cost ] at *;
      rcases ‹z = 0 ∧ w = 1 ∨ z = 1 ∧ w = 0 ∨ z = 1 ∧ w = 1› with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> rcases ‹2 = u ∧ 0 = v ∨ 1 = u ∧ 1 = v ∨ 1 = u ∧ 0 = v› with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> trivial;
    · bound;
    · grind); exact (by
  -- The minimum cost to reach (0,0) is simply the value at that cell, which is 1.
  simp [ensures3];
  decide +revert)

-- test2
lemma test2_precondition :
  precondition test2_cost test2_m test2_n := by
  constructor <;> simp +decide [ test2_cost, test2_m, test2_n ];
  · -- The cost matrix is non-empty and each row has the same length as the first row.
    simp [require1, require2, require3];
  · unfold require2 require3 require4 require5; aesop;

lemma test2_postcondition :
  postcondition test2_cost test2_m test2_n test2_Expected := by
  -- For the test case 2, the cost matrix is a single cell with value 5. The start and end are both (0, 0). The preconditions are satisfied because the matrix is non-empty and has the correct dimensions.
  simp [postcondition, test2_cost, test2_m, test2_n, test2_Expected];
  -- The path [ (0,0) ] satisfies the conditions for validity, cost, and the edge case.
  simp [ensures1, ensures2, ensures3, isValidPath, pathCost];
  constructor;
  · -- The path [(0,0)] satisfies all conditions.
    use [(0, 0)]
    simp;
  · intro path h1 h2 h3 h4; induction path using List.reverseRecOn <;> aesop;

-- test3
lemma test3_precondition :
  precondition test3_cost test3_m test3_n := by
  -- Verify that the cost matrix is non-empty.
  simp [precondition, require1, require2, require3, require4, require5];
  native_decide +revert

lemma test3_postcondition :
  postcondition test3_cost test3_m test3_n test3_Expected := by
  -- Let's verify the postcondition for the test case 3.
  apply And.intro;
  · -- Let's construct the path [(0,0), (1,1)] and show that it satisfies the conditions.
    use [(0, 0), (1, 1)];
    -- Verify that the path [(0,0), (1,1)] is valid and its cost is 2.
    simp [isValidPath, pathCost, test3_m, test3_n, test3_Expected];
    exact ⟨ fun i hi => by rcases i with ( _ | _ | i ) <;> trivial, rfl ⟩;
  · unfold ensures2 ensures3; aesop;
    · -- Let's consider the possible paths from (0,0) to (1,1) in the test3_cost matrix.
      have h_paths : ∀ path : List (ℕ × ℕ), isValidPath path 0 0 1 1 → pathCost test3_cost path ≥ 2 := by
        intros path hpath
        rcases path with ( _ | ⟨ _, _ | ⟨ _, _ | path ⟩ ⟩ ) <;> norm_num at *;
        · cases hpath.1;
        · cases hpath ; aesop;
        · unfold isValidPath at hpath; aesop;
        · cases hpath ; aesop;
          have := right 0; have := right 1; norm_num at * ; aesop;
          all_goals unfold pathCost; simp +arith +decide [ test3_cost ];
          -- Since each step adds at least 1 to the accumulator, the minimum possible value after processing the tail is 2.
          have h_min : ∀ (acc : ℕ) (tail : List (ℕ × ℕ)), 2 ≤ acc → 2 ≤ List.foldl (fun (acc : ℕ) (x : ℕ × ℕ) => acc + ([#[1, 10], #[10, 1]][x.1]?.getD Inhabited.default)[x.2]!) acc tail := by
            intro acc tail hacc; induction tail using List.reverseRecOn <;> aesop;
            exact le_add_right a_2;
          exact h_min _ _ ( by norm_num );
          have h_min : ∀ (acc : ℕ) (tail : List (ℕ × ℕ)), 2 ≤ acc → 2 ≤ List.foldl (fun (acc : ℕ) (x : ℕ × ℕ) => acc + ([#[1, 10], #[10, 1]][x.1]?.getD Inhabited.default)[x.2]!) acc tail := by
            intro acc tail hacc; induction tail using List.reverseRecOn <;> aesop;
            exact le_add_right a_2
          exact h_min _ _ ( by norm_num ) ;
          have h_min : ∀ (acc : ℕ) (tail : List (ℕ × ℕ)), 2 ≤ acc → 2 ≤ List.foldl (fun (acc : ℕ) (x : ℕ × ℕ) => acc + ([#[1, 10], #[10, 1]][x.1]?.getD Inhabited.default)[x.2]!) acc tail := by
            intro acc tail hacc; induction tail using List.reverseRecOn <;> aesop;
            exact le_add_right a_2 |> le_trans ( by norm_num ) ;
          exact h_min _ _ ( by norm_num );
          have h_min : ∀ (acc : ℕ) (tail : List (ℕ × ℕ)), 2 ≤ acc → 2 ≤ List.foldl (fun (acc : ℕ) (x : ℕ × ℕ) => acc + ([#[1, 10], #[10, 1]][x.1]?.getD Inhabited.default)[x.2]!) acc tail := by
            intros acc tail hacc; induction' tail using List.reverseRecOn with tail ih <;> aesop;
            exact le_add_right a_1
          exact h_min _ _ ( by norm_num );
          · -- Since each step adds at least 1 to the accumulator, the minimum possible value after processing the tail is 2. Therefore, the inequality holds.
            have h_min : ∀ (acc : ℕ) (tail : List (ℕ × ℕ)), 2 ≤ acc → 2 ≤ List.foldl (fun (acc : ℕ) (x : ℕ × ℕ) => acc + ([#[1, 10], #[10, 1]][x.1]?.getD Inhabited.default)[x.2]!) acc tail := by
              intros acc tail hacc; induction' tail using List.reverseRecOn with tail ih <;> aesop;
              exact le_add_right a_1
            exact h_min _ _ ( by norm_num );
          · induction tail using List.reverseRecOn <;> aesop;
            exact le_add_of_le_of_nonneg ( Nat.le_trans ( by norm_num ) ( show List.foldl ( fun acc x => acc + ( [ #[1, 10], #[10, 1] ][ x.1 ]?.getD Inhabited.default )[ x.2 ]! ) 11 l ≥ 11 from by
                                                                            have h_min : ∀ (acc : ℕ) (tail : List (ℕ × ℕ)), 11 ≤ acc → 11 ≤ List.foldl (fun (acc : ℕ) (x : ℕ × ℕ) => acc + ([#[1, 10], #[10, 1]][x.1]?.getD Inhabited.default)[x.2]!) acc tail := by
                                                                              intros acc tail hacc; induction tail using List.reverseRecOn <;> aesop;
                                                                              exact le_add_right a_3;
                                                                            exact h_min _ _ ( by norm_num ) ) ) ( Nat.zero_le _ );
          · have h_min : ∀ (acc : ℕ) (tail : List (ℕ × ℕ)), 11 ≤ acc → 2 ≤ List.foldl (fun (acc : ℕ) (x : ℕ × ℕ) => acc + ([#[1, 10], #[10, 1]][x.1]?.getD Inhabited.default)[x.2]!) acc tail := by
              intros acc tail hacc; induction' tail using List.reverseRecOn with tail ih <;> aesop;
              · linarith;
              · exact le_add_of_le_of_nonneg a_1 ( Nat.zero_le _ )
            exact h_min _ _ ( by norm_num );
          · -- Since each step in the foldl adds at least 1 to the accumulator, starting from 2, the result is at least 2.
            have h_min : ∀ (acc : ℕ) (tail : List (ℕ × ℕ)), 2 ≤ acc → 2 ≤ List.foldl (fun (acc : ℕ) (x : ℕ × ℕ) => acc + ([#[1, 10], #[10, 1]][x.1]?.getD Inhabited.default)[x.2]!) acc tail := by
              intro acc tail hacc; induction tail using List.reverseRecOn <;> aesop;
              exact le_add_right a_2;
            exact h_min _ _ ( by norm_num );
          · have h_min : ∀ (acc : ℕ) (tail : List (ℕ × ℕ)), 2 ≤ acc → 2 ≤ List.foldl (fun (acc : ℕ) (x : ℕ × ℕ) => acc + ([#[1, 10], #[10, 1]][x.1]?.getD Inhabited.default)[x.2]!) acc tail := by
              intro acc tail hacc; induction tail using List.reverseRecOn <;> aesop;
              exact le_add_right a_2
            exact h_min _ _ ( by norm_num );
      exact h_paths path a;
    · contradiction

-- test4
lemma test4_precondition :
  precondition test4_cost test4_m test4_n := by
  -- Check that the cost matrix is non-empty.
  simp [precondition, require1, require2, require3, require4, require5];
  native_decide +revert

lemma test4_postcondition :
  postcondition test4_cost test4_m test4_n test4_Expected := by
  constructor;
  · -- The minimum cost path is [(0,0), (1,1), (2,2)] with a total cost of 3.
    use [(0,0), (1,1), (2,2)];
    -- Let's verify the validity of the path and the cost calculation.
    simp [isValidPath, pathCost, test4_cost, test4_m, test4_n, test4_Expected];
    rintro ( _ | _ | i ) hi <;> trivial;
  · aesop;
    · -- To prove the second part of the postcondition, we need to show that any valid path from (0,0) to (2,2) has a cost of at least 3.
      intro path hpath
      obtain ⟨hpath_start, hpath_end, hpath_valid⟩ := hpath;
      -- By definition of `pathCost`, we need to show that the sum of the costs of the cells visited along the path is at least 3.
      have h_cost : ∀ p ∈ path, (test4_cost[p.1]!)[p.2]! ≥ 1 := by
        intro p hp
        have h_bounds : p.1 < 3 ∧ p.2 < 3 := by
          have h_bounds : ∀ p ∈ path, p.1 ≤ path.getLast?.get!.1 ∧ p.2 ≤ path.getLast?.get!.2 := by
            intro p hp
            have h_bounds : ∀ i < path.length, (path[i]!).1 ≤ (path.getLast?.get!).1 ∧ (path[i]!).2 ≤ (path.getLast?.get!).2 := by
              -- By induction on the length of the path, we can show that each element's coordinates are less than or equal to the last element's coordinates.
              have h_ind : ∀ i < path.length, ∀ j, i ≤ j → j < path.length → (path[i]!).1 ≤ (path[j]!).1 ∧ (path[i]!).2 ≤ (path[j]!).2 := by
                intro i hi j hij hj; induction hij <;> aesop;
                · grind;
                · grind;
              intro i hi; specialize h_ind i hi ( List.length path - 1 ) ( Nat.le_sub_one_of_lt hi ) ( Nat.sub_lt hpath_start zero_lt_one ) ; aesop;
              · grind;
              · grind;
            obtain ⟨ i, hi ⟩ := List.mem_iff_get.1 hp;
            simpa [ ← hi ] using h_bounds i i.2;
          aesop;
          · exact lt_of_le_of_lt ( h_bounds _ _ hp |>.1 ) ( by decide );
          · exact lt_of_le_of_lt ( h_bounds _ _ hp |>.2 ) ( by decide );
        rcases h_bounds with ⟨ h₁, h₂ ⟩ ; interval_cases p.1 <;> interval_cases p.2 <;> trivial;
      -- Applying the hypothesis `h_cost` to each element in the path, we can sum the costs.
      have h_sum_cost : path.foldl (fun acc p => acc + (test4_cost[p.1]!)[p.2]!) 0 ≥ path.length * 1 := by
        have h_sum_cost : ∀ {l : List (ℕ × ℕ)}, (∀ p ∈ l, (test4_cost[p.1]!)[p.2]! ≥ 1) → l.foldl (fun acc p => acc + (test4_cost[p.1]!)[p.2]!) 0 ≥ l.length * 1 := by
          intros l hl; induction' l using List.reverseRecOn with p l ih <;> aesop;
          linarith [ hl fst snd ( Or.inr ⟨ rfl, rfl ⟩ ) ];
        apply h_sum_cost; assumption;
      -- Since the length of the path is at least 3, we can conclude that the sum of the costs is at least 3.
      have h_length : path.length ≥ 3 := by
        rcases path with ( _ | ⟨ ⟨ x, y ⟩, _ | ⟨ ⟨ u, v ⟩, _ | ⟨ ⟨ w, z ⟩, _ | path ⟩ ⟩ ⟩ ) <;> simp_all +arith +decide;
        -- Since $u$ and $v$ are either $(0,1)$, $(1,0)$, or $(1,1)$, and $test4_m = 2$ and $test4_n = 2$, this leads to a contradiction.
        aesop;
        · contradiction;
        · -- The contradiction arises because the assumptions `left` and `right` are incorrect. The correct values for `test4_m` and `test4_n` are 2 and 2, respectively.
          cases left;
        · -- The contradiction arises because `left` and `right` are incorrectly defined as `test4_m = 1` and `test4_n = 1`, but in the test case, `test4_m` and `test4_n` are actually 2. This means that the assumptions `left` and `right` are incorrect, leading to a contradiction.
          norm_num [test4_m, test4_n] at *;
      exact le_trans ( by decide ) ( h_sum_cost.trans' ( Nat.mul_le_mul_right _ h_length ) );
    · -- Since $m = 2$ and $n = 2$, the antecedent $m = 0 \land n = 0$ is false, making the implication trivially true.
      simp [ensures3];
      decide +revert

-- test7
lemma test7_precondition :
  precondition test7_cost test7_m test7_n := by
  -- Check that the cost matrix is non-empty.
  simp [precondition, test7_cost, test7_m, test7_n];
  -- Check that the cost matrix is non-empty and all rows have the same length.
  simp [require1, require2, require3, require4, require5];
  native_decide

lemma test7_postcondition :
  postcondition test7_cost test7_m test7_n test7_Expected := by
  constructor;
  · -- Construct the path [(0, 0), (1, 1), (2, 2)] and show it is valid.
    use [(0, 0), (1, 1), (2, 2)];
    simp +decide [ isValidPath, pathCost ];
    rintro ( _ | _ | _ | i ) hi <;> trivial;
  · -- For the test7 case, we need to show that any valid path has a cost of at least 3.
    have h_test7_ensures2 : ∀ path : List (Nat × Nat), isValidPath path 0 0 2 2 → pathCost test7_cost path ≥ 3 := by
      -- By definition of `isValidPath`, any valid path from (0,0) to (2,2) must have at least three steps.
      intros path hpath
      have h_len : path.length ≥ 3 := by
        unfold isValidPath at hpath;
        rcases path with ( _ | ⟨ ⟨ x, y ⟩, _ | ⟨ ⟨ z, w ⟩, _ | path ⟩ ⟩ ) <;> simp_all +arith +decide;
        · linarith;
        · omega;
      -- Since each step in the path adds 1 to the cost and the path has at least 3 steps, the total cost is at least 3.
      have h_cost : ∀ i < path.length, (test7_cost[path[i]!.1]!)[path[i]!.2]! = 1 := by
        have h_coords : ∀ i < path.length, path[i]!.1 ≤ 2 ∧ path[i]!.2 ≤ 2 := by
          -- By definition of `isValidPath`, each step in the path is either right, down, or diagonal down-right.
          have h_step_bounds : ∀ i < path.length - 1, path[i]!.1 ≤ path[i + 1]!.1 ∧ path[i]!.2 ≤ path[i + 1]!.2 := by
            intro i hi; have := hpath.2.2.2 i ( by omega ) ; aesop;
          -- By induction on $i$, we can show that for any $i < \text{length}$, the coordinates of the $i$-th element are less than or equal to the coordinates of the last element.
          have h_ind : ∀ i < path.length, path[i]!.1 ≤ path.getLast!.1 ∧ path[i]!.2 ≤ path.getLast!.2 := by
            intro i hi;
            have h_ind : ∀ j, i ≤ j → j < path.length → path[i]!.1 ≤ path[j]!.1 ∧ path[i]!.2 ≤ path[j]!.2 := by
              -- By induction on $j$, we can show that for any $j \geq i$, the coordinates of the $i$-th element are less than or equal to those of the $j$-th element.
              intros j hij hj
              induction' hij with j hj ih;
              · norm_num;
              · exact ⟨ le_trans ( ih ( Nat.lt_of_succ_lt hj ) |>.1 ) ( h_step_bounds _ ( Nat.lt_pred_iff.mpr hj ) |>.1 ), le_trans ( ih ( Nat.lt_of_succ_lt hj ) |>.2 ) ( h_step_bounds _ ( Nat.lt_pred_iff.mpr hj ) |>.2 ) ⟩;
            grind;
          cases hpath ; aesop;
        intro i hi; specialize h_coords i hi; rcases h_coords with ⟨ h₁, h₂ ⟩ ; interval_cases path[i]!.1 <;> interval_cases path[i]!.2 <;> trivial;
      have h_sum : pathCost test7_cost path = Finset.sum (Finset.range path.length) (fun i => (test7_cost[path[i]!.1]!)[path[i]!.2]!) := by
        have h_sum : ∀ (l : List (Nat × Nat)), List.foldl (fun acc (x : Nat × Nat) => acc + (test7_cost[x.1]!)[x.2]!) 0 l = Finset.sum (Finset.range l.length) (fun i => (test7_cost[l[i]!.1]!)[l[i]!.2]!) := by
          intro l; induction' l using List.reverseRecOn with l ih <;> aesop;
          simp +arith +decide [ Finset.sum_range_succ ];
          exact Finset.sum_congr rfl fun x hx => by rw [ List.getElem?_append ] ; aesop;
        apply h_sum;
      rw [ h_sum, Finset.sum_congr rfl fun i hi => h_cost i <| Finset.mem_range.mp hi ] ; norm_num ; linarith;
    exact ⟨ h_test7_ensures2, by rintro ⟨ ⟩ ; trivial ⟩

-- test12
lemma test12_precondition :
  precondition test12_cost test12_m test12_n := by
  -- By definition of `precondition`, we need to show that `test12_cost` satisfies all the required conditions.
  unfold precondition;
  unfold require1 require2 require3 require4 require5; simp_all +decide ;

lemma test12_postcondition :
  postcondition test12_cost test12_m test12_n test12_Expected := by
  unfold test12_cost test12_m test12_n test12_Expected postcondition;
  aesop;
  · -- Let's choose the path (0,0) → (0,1) → (1,2) → (2,2).
    use [(0,0), (0,1), (1,2), (2,2)];
    -- Let's verify the path and calculate its cost.
    simp [isValidPath, pathCost];
    rintro ( _ | _ | _ | i ) hi <;> trivial;
  · -- Let's consider all possible paths from (0,0) to (2,2) and show that their costs are at least 4. We can do this by enumerating all possible paths and calculating their costs.
    have h_paths : ∀ path : List (Nat × Nat), isValidPath path 0 0 2 2 → pathCost #[#[1, 1, 1], #[1, 100, 1], #[1, 1, 1]] path ≥ 4 := by
      intro path hpath
      have h_len : path.length ≤ 5 := by
        have := hpath.2.2.2;
        -- By induction on the length of the path, we can show that the sum of the coordinates of the last element is at least the length of the path minus one.
        have h_sum : ∀ i < path.length, (path[i]!).1 + (path[i]!).2 ≥ i := by
          intro i hi; induction' i with i ih <;> aesop;
          grind +ring;
        have := hpath.2.2.1; aesop;
        grind
      rcases path with ( _ | ⟨ p, _ | ⟨ q, _ | ⟨ r, _ | ⟨ s, _ | ⟨ t, _ | path ⟩ ⟩ ⟩ ⟩ ⟩ ) <;> simp_all +arith +decide;
      all_goals unfold isValidPath at hpath; simp_all +arith +decide [ pathCost ] ;
      · aesop;
      · aesop;
      · have := hpath.2.2 0; have := hpath.2.2 1; aesop;
      · have := hpath.2.2 0; have := hpath.2.2 1; have := hpath.2.2 2; simp_all +decide ;
        rcases q with ⟨ _ | _ | q₁, _ | _ | q₂ ⟩ <;> rcases r with ⟨ _ | _ | r₁, _ | _ | r₂ ⟩ <;> simp_all +arith +decide only [ ] ;
        all_goals aesop ( simp_config := { decide := true } ) ;
      · have := hpath.2.2 0; have := hpath.2.2 1; have := hpath.2.2 2; have := hpath.2.2 3; simp_all +arith +decide;
        rcases this with ( ⟨ hs₁, hs₂ ⟩ | ⟨ hs₁, hs₂ ⟩ | ⟨ hs₁, hs₂ ⟩ ) <;> rcases ‹q.1 = 0 ∧ q.2 = 1 ∨ q.1 = 1 ∧ q.2 = 0 ∨ q.1 = 1 ∧ q.2 = 1› with ( ⟨ hq₁, hq₂ ⟩ | ⟨ hq₁, hq₂ ⟩ | ⟨ hq₁, hq₂ ⟩ ) <;> rcases ‹r.1 = q.1 ∧ r.2 = q.2 + 1 ∨ r.1 = q.1 + 1 ∧ r.2 = q.2 ∨ r.1 = q.1 + 1 ∧ r.2 = q.2 + 1› with ( ⟨ hr₁, hr₂ ⟩ | ⟨ hr₁, hr₂ ⟩ | ⟨ hr₁, hr₂ ⟩ ) <;> simp_all +arith +decide only;
        all_goals norm_num [ ← hs₂ ] at *;
        · norm_num [ ← hs₁ ];
        · norm_num [ ← hs₁ ];
        · norm_num [ ← hs₁ ] at *;
        · linarith;
        · linarith;
    assumption;
  · exact fun h => by aesop;

-----------------------------
-- Uniqueness Verification --
-----------------------------
lemma uniqueness (cost: Array (Array Nat)) (m: Nat) (n: Nat):
  precondition cost m n →
  (∀ ret1 ret2,
    postcondition cost m n ret1 →
    postcondition cost m n ret2 →
    ret1 = ret2) := by
  bound;
  -- By definition of postcondition, we know that both ret1 and ret2 satisfy the ensures2 condition.
  have h_ensures2 : ∀ path, isValidPath path 0 0 m n → pathCost cost path ≥ ret1 ∧ pathCost cost path ≥ ret2 := by
    -- By definition of postcondition, we know that both ret1 and ret2 satisfy the ensures2 condition, which states that for any valid path, the path cost is at least ret1 and ret2.
    intros path hpath
    exact ⟨a_1.2.1 path hpath, a_2.2.1 path hpath⟩;
  obtain ⟨ path, hpath ⟩ := a_1.1;
  obtain ⟨ path', hpath' ⟩ := a_2.1;
  grind
