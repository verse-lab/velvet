import Lean
import Mathlib.Tactic

-- Helper Functions

inductive IntOrString where
  | int : Int → IntOrString
  | str : String → IntOrString
  deriving Inhabited, DecidableEq, Repr

def isInt (elem : IntOrString) : Bool :=
  match elem with
  | IntOrString.int _ => true
  | IntOrString.str _ => false

def isString (elem : IntOrString) : Bool :=
  match elem with
  | IntOrString.int _ => false
  | IntOrString.str _ => true

def IntOrString.le (a b : IntOrString) : Prop :=
  match a, b with
  | IntOrString.int i1, IntOrString.int i2 => i1 ≤ i2
  | IntOrString.int _, IntOrString.str _ => True  -- integers come before strings
  | IntOrString.str _, IntOrString.int _ => False -- strings come after integers
  | IntOrString.str s1, IntOrString.str s2 => s1 ≤ s2  -- lexicographic order

def isSorted (lst : List IntOrString) : Prop :=
  ∀ i, i + 1 < lst.length → IntOrString.le lst[i]! lst[i+1]!

def isPermutation (lst1 lst2 : List IntOrString) : Prop :=
  lst1.length = lst2.length ∧
  (∀ elem ∈ lst1, (lst1.filter (· == elem)).length = (lst2.filter (· == elem)).length) ∧
  (∀ elem ∈ lst2, (lst1.filter (· == elem)).length = (lst2.filter (· == elem)).length)

def ensures1 (input : List IntOrString) (result : List IntOrString) :=
  isPermutation input result  -- result is a permutation of input
def ensures2 (input : List IntOrString) (result : List IntOrString) :=
  isSorted result  -- result is sorted according to our ordering
def ensures3 (input : List IntOrString) (result : List IntOrString) :=
  ∀ i j, i < result.length ∧ j < result.length ∧
            isInt result[i]! ∧ isString result[j]! → i < j  -- integers come before strings

def precondition (input: List IntOrString) :=
  True

def postcondition (input: List IntOrString) (result: List IntOrString) :=
  ensures1 input result ∧ ensures2 input result ∧ ensures3 input result

-- Test Cases
def test0_Input : List IntOrString :=
  [IntOrString.int 19, IntOrString.str "red", IntOrString.int 12,
   IntOrString.str "green", IntOrString.str "blue", IntOrString.int 10,
   IntOrString.str "white", IntOrString.str "green", IntOrString.int 1]

def test0_Expected : List IntOrString :=
  [IntOrString.int 1, IntOrString.int 10, IntOrString.int 12, IntOrString.int 19,
   IntOrString.str "blue", IntOrString.str "green", IntOrString.str "green",
   IntOrString.str "red", IntOrString.str "white"]

def test1_Input : List IntOrString :=
  [IntOrString.int 5, IntOrString.str "apple", IntOrString.int 2,
   IntOrString.str "banana", IntOrString.int 8, IntOrString.str "cherry"]

def test1_Expected : List IntOrString :=
  [IntOrString.int 2, IntOrString.int 5, IntOrString.int 8,
   IntOrString.str "apple", IntOrString.str "banana", IntOrString.str "cherry"]

def test2_Input : List IntOrString :=
  [IntOrString.int 10, IntOrString.int 3, IntOrString.int 7, IntOrString.int 1]

def test2_Expected : List IntOrString :=
  [IntOrString.int 1, IntOrString.int 3, IntOrString.int 7, IntOrString.int 10]

def test3_Input : List IntOrString :=
  [IntOrString.str "zebra", IntOrString.str "apple", IntOrString.str "mango", IntOrString.str "banana"]

def test3_Expected : List IntOrString :=
  [IntOrString.str "apple", IntOrString.str "banana", IntOrString.str "mango", IntOrString.str "zebra"]

def test6_Input : List IntOrString :=
  [IntOrString.int (-5), IntOrString.str "delta", IntOrString.int 100,
   IntOrString.int (-10), IntOrString.str "alpha", IntOrString.int 0, IntOrString.str "beta"]

def test6_Expected : List IntOrString :=
  [IntOrString.int (-10), IntOrString.int (-5), IntOrString.int 0, IntOrString.int 100,
   IntOrString.str "alpha", IntOrString.str "beta", IntOrString.str "delta"]

def test7_Input : List IntOrString :=
  [IntOrString.int 5, IntOrString.str "apple", IntOrString.int 5,
   IntOrString.str "apple", IntOrString.int 3]

def test7_Expected : List IntOrString :=
  [IntOrString.int 3, IntOrString.int 5, IntOrString.int 5,
   IntOrString.str "apple", IntOrString.str "apple"]

-------------------------------
-- Verifications
-------------------------------

----------------------------
-- Verification: test0
----------------------------
lemma test0_precondition :
  precondition test0_Input := by
  trivial

lemma test0_postcondition :
  postcondition test0_Input test0_Expected := by
  -- Show that the expected output is a permutation of the input.
  have h_perm : isPermutation test0_Input test0_Expected := by
    unfold isPermutation;
    -- Show that the lengths of the input and expected output lists are equal.
    simp +decide [test0_Input, test0_Expected];
  -- Check that the expected output is sorted according to the given ordering.
  have h_sorted : isSorted test0_Expected := by
    -- Check that each adjacent pair in the expected output is in order.
    intro i hi
    simp [test0_Expected];
    rcases i with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | i ) <;> norm_num at hi ⊢;
    all_goals norm_cast;
    all_goals unfold IntOrString.le; norm_num;
    · decide +revert;
    · decide +revert;
    · decide +revert;
  -- Check that all integers come before all strings in the expected output.
  have h_int_str_order : ∀ i j, i < test0_Expected.length ∧ j < test0_Expected.length ∧ isInt test0_Expected[i]! ∧ isString test0_Expected[j]! → i < j := by
    simp +decide [ test0_Expected ];
    intro i j hi hj hi' hj'; interval_cases i <;> interval_cases j <;> trivial;
  -- Combine the three conditions to conclude the postcondition.
  apply And.intro h_perm (And.intro h_sorted h_int_str_order)

----------------------------
-- Verification: test1
----------------------------
lemma test1_precondition :
  precondition test1_Input := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test1_postcondition :
  postcondition test1_Input test1_Expected := by
  constructor;
  · -- To prove the permutation property, we can use the fact that the lists have the same elements with the same frequencies.
    apply And.intro;
    · native_decide +revert;
    · -- By definition of permutation, the counts of each element in the input and expected lists are the same.
      simp [test1_Input, test1_Expected];
  · aesop;
    · -- Check that each adjacent pair in the expected list satisfies the IntOrString.le condition.
      simp [ensures2, IntOrString.le];
      -- The integers in the expected result are already in ascending order.
      simp [isSorted, test1_Expected];
      -- Check each pair of adjacent elements in the list.
      intro i hi
      interval_cases _ : i + 1 <;> simp_all +decide;
      · -- Since 2 is less than or equal to 5, we have IntOrString.int 2 ≤ IntOrString.int 5.
        apply Int.le_of_lt; norm_num;
      · -- Since 5 is less than 8, we have IntOrString.le (IntOrString.int 5) (IntOrString.int 8).
        apply le_of_lt; norm_num;
      · exact?;
      · -- Since "apple" comes before "banana" in lexicographic order, we have "apple" ≤ "banana".
        simp [IntOrString.le]
      · -- Since "banana" comes before "cherry" in lexicographic order, we have "banana" ≤ "cherry".
        simp [IntOrString.le]
    · -- In the test1_Expected list, the integers are at indices 0, 1, 2, and the strings start at index 3. Therefore, for any i < j, if the element at i is an integer and the element at j is a string, then i < j.
      intros i j hij
      aesop;
      rcases i with ( _ | _ | _ | _ | _ | _ | i ) <;> rcases j with ( _ | _ | _ | _ | _ | _ | j ) <;> trivial

----------------------------
-- Verification: test2
----------------------------
lemma test2_precondition :
  precondition test2_Input := by
  -- The precondition is trivially true for any input.
  apply trivial

lemma test2_postcondition :
  postcondition test2_Input test2_Expected := by
  constructor;
  · -- We'll use the fact that the lengths of the input and expected lists are equal.
    unfold ensures1;
    -- By definition of `isPermutation`, we need to show that the lengths of the input and expected lists are equal.
    simp [isPermutation, test2_Input, test2_Expected];
  · unfold ensures2 ensures3;
    aesop;
    · -- We can verify that the list is sorted by checking each pair of adjacent elements.
      simp [isSorted, test2_Expected];
      rintro ( _ | _ | _ | i ) hi <;> norm_cast;
      · exact show 1 ≤ 3 by decide;
      · exact show 3 ≤ 7 from by decide;
      · -- Since 7 ≤ 10 is true, we can conclude the proof.
        norm_num [IntOrString.le];
    · rcases i with ( _ | _ | _ | _ | i ) <;> rcases j with ( _ | _ | _ | _ | j ) <;> trivial

----------------------------
-- Verification: test3
----------------------------
lemma test3_precondition :
  precondition test3_Input := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test3_postcondition :
  postcondition test3_Input test3_Expected := by
  -- Verify that the result is a permutation of the input.
  have h_perm : isPermutation test3_Input test3_Expected := by
    simp +decide [ isPermutation ];
  -- Verify that the result is sorted according to our ordering.
  have h_sorted : isSorted test3_Expected := by
    intro i hi;
    -- By examining each pair of adjacent elements in the list, we can verify that they are sorted according to the IntOrString.le relation.
    have h_sorted : ∀ i < 3, test3_Expected[i]!.le test3_Expected[i + 1]! := by
      simp +decide [ IntOrString.le ];
      intro i hi; interval_cases i <;> simp +decide [ test3_Expected ] ;
    exact h_sorted i ( by norm_num [ test3_Expected ] at hi; linarith );
  constructor <;> aesop;
  unfold test3_Input test3_Expected ensures3; aesop;
  interval_cases i <;> interval_cases j <;> trivial

----------------------------
-- Verification: test6
----------------------------
lemma test6_precondition :
  precondition test6_Input := by
  exact?

lemma test6_postcondition :
  postcondition test6_Input test6_Expected := by
  -- Now let's verify that the postcondition holds for test6_Input and test6_Expected.
  apply And.intro;
  · constructor <;> norm_cast;
  · -- Now let's verify that the postcondition holds for test6_Input and test6_Expected. We'll start with ensures2.
    apply And.intro;
    · -- By examining each pair of adjacent elements in the list, we can verify that they are in the correct order according to the IntOrString.le relation.
      intros i hi
      simp [test6_Expected] at hi ⊢;
      -- By examining each pair of adjacent elements in the list, we can verify that they are in the correct order according to the IntOrString.le relation. We'll check each case individually.
      interval_cases _ : i + 1 <;> simp_all +decide [ IntOrString.le ];
    · intro i j h; rcases i with ( _ | _ | _ | _ | _ | _ | _ | i ) <;> rcases j with ( _ | _ | _ | _ | _ | _ | _ | j ) <;> norm_num at h ⊢ <;> tauto;

----------------------------
-- Verification: test7
----------------------------
lemma test7_precondition :
  precondition test7_Input := by
  exact?

lemma test7_postcondition :
  postcondition test7_Input test7_Expected := by
  -- Let's verify the postcondition for test7.
  apply And.intro;
  · constructor <;> simp +decide [ List.pairwise_iff_get ];
  · constructor;
    · -- Let's verify each pair of adjacent elements in the list.
      intro i hi
      rcases i with ( _ | _ | _ | _ | i ) <;> norm_num [ test7_Expected ] at hi ⊢;
      · -- Since 3 and 5 are both integers, we can use the fact that 3 ≤ 5 in the integers.
        apply le_of_lt; norm_num;
      · -- Since 5 is equal to itself, the inequality holds.
        apply le_refl;
      · trivial;
      · -- Since "apple" is equal to itself, the inequality holds.
        simp [IntOrString.le];
      · grind;
    · -- We need to show that for any $i$ and $j$, if the $i$-th element is an integer and the $j$-th element is a string, then $i < j$.
      intros i j hij
      aesop;
      rcases i with ( _ | _ | _ | _ | _ | i ) <;> rcases j with ( _ | _ | _ | _ | _ | j ) <;> trivial;

-----------------------------
-- Uniqueness Verification --
-----------------------------

lemma uniqueness (input: List IntOrString):
  precondition input →
  (∀ ret1 ret2,
    postcondition input ret1 →
    postcondition input ret2 →
    ret1 = ret2) := by
  -- If two lists are permutations of each other and both are sorted, they must be equal.
  intros h_pre ret1 ret2 h_ret1 h_ret2
  have h_perm : List.Perm ret1 ret2 := by
    -- Since ret1 and ret2 are both permutations of the input, they must be permutations of each other.
    have h_perm : List.Perm ret1 input ∧ List.Perm ret2 input := by
      cases h_ret1 ; cases h_ret2 ; aesop;
      · unfold ensures1 at *;
        rw [ List.perm_iff_count ];
        intro a; have := left; unfold isPermutation at this; aesop;
        by_cases ha : a ∈ input <;> by_cases ha' : a ∈ ret1 <;> simp_all +decide [ List.count ];
        · rw [ List.countP_eq_length_filter, List.countP_eq_length_filter ] ; aesop;
        · grind;
        · specialize right_2 a ha'; simp_all +decide [ List.countP_eq_length_filter ] ;
        · rw [ List.countP_eq_zero.mpr, List.countP_eq_zero.mpr ] <;> aesop;
      · rw [ List.perm_iff_count ];
        cases left_1 ; aesop;
        by_cases ha : a ∈ input <;> by_cases hb : a ∈ ret2 <;> simp_all +decide [ List.count ];
        · rw [ List.countP_eq_length_filter, List.countP_eq_length_filter ] ; aesop;
        · specialize left_4 a ha; specialize right_2 a; simp_all +decide [ List.countP_eq_length_filter ] ;
        · specialize right_2 a hb; simp_all +decide [ List.countP_eq_length_filter ] ;
        · rw [ List.countP_eq_zero.mpr, List.countP_eq_zero.mpr ] <;> aesop;
    exact h_perm.1.trans h_perm.2.symm;
  have h_sorted : List.Sorted (fun x y => IntOrString.le x y) ret1 ∧ List.Sorted (fun x y => IntOrString.le x y) ret2 := by
    unfold postcondition at * ; aesop;
    · convert left_2 using 1;
      ext;
      unfold ensures2; aesop;
      · intro i hi; have := a; aesop;
        have := List.pairwise_iff_get.mp this;
        convert this ⟨ i, by linarith ⟩ ⟨ i + 1, by linarith ⟩ ( Nat.lt_succ_self _ ) using 1;
        grind;
      · refine' List.pairwise_iff_get.mpr _;
        intro i j hij; induction j ; induction i ; aesop;
        induction hij <;> aesop;
        · convert a val_1 isLt using 1;
          · exact?;
          · grind;
        · -- By transitivity of the le relation, we have x[val_1].le x[m + 1].
          have h_trans : x[val_1].le x[m] ∧ x[m].le x[m + 1] := by
            -- By the induction hypothesis, we have x[val_1].le x[m].
            have h_ind : x[val_1].le x[m] := by
              exact a_ih ( Nat.lt_of_succ_lt isLt );
            -- By the definition of `isSorted`, we know that `x[m].le x[m + 1]` since `m + 1 < x.length`.
            have h_sorted : x[m].le x[m + 1] := by
              convert a m ( by linarith ) using 1;
              · grind;
              · grind
            exact ⟨h_ind, h_sorted⟩;
          cases h : x[val_1] <;> cases h' : x[m] <;> cases h'' : x[m + 1] <;> aesop;
          · exact le_trans left_4 right_2;
          · cases right_2;
          · cases left_4;
          · exact String.le_trans left_4 right_2;
    · -- By definition of `ensures2`, we know that `ret2` is sorted.
      convert left_3 using 1;
      ext;
      unfold ensures2; aesop;
      · intro i hi; have := a; aesop;
        have := List.pairwise_iff_get.mp this;
        convert this ⟨ i, by linarith ⟩ ⟨ i + 1, by linarith ⟩ ( Nat.lt_succ_self _ ) using 1;
        grind;
      · refine' List.pairwise_iff_get.mpr _;
        intro i j hij; induction j ; induction i ; aesop;
        induction hij <;> aesop;
        · convert a val_1 isLt using 1;
          · exact?;
          · grind;
        · -- By transitivity of the le relation, we have x[val_1].le x[m + 1].
          have h_trans : x[val_1].le x[m] ∧ x[m].le x[m + 1] := by
            -- By the induction hypothesis, we have x[val_1].le x[m].
            have h_ind : x[val_1].le x[m] := by
              exact a_ih ( Nat.lt_of_succ_lt isLt );
            -- By the definition of `isSorted`, we know that `x[m].le x[m + 1]` since `m + 1 < x.length`.
            have h_sorted : x[m].le x[m + 1] := by
              convert a m ( by linarith ) using 1;
              · grind;
              · grind
            exact ⟨h_ind, h_sorted⟩;
          cases h : x[val_1] <;> cases h' : x[m] <;> cases h'' : x[m + 1] <;> aesop;
          · exact le_trans left_4 right_2;
          · cases right_2;
          · cases left_4;
          · exact String.le_trans left_4 right_2;
  apply_rules [ List.eq_of_perm_of_sorted ];
  exact h_sorted.1;
  · exact h_sorted.2;
  · constructor;
    aesop;
    cases a <;> cases b <;> aesop;
    · exact le_antisymm a_1 a_2;
    · exact String.le_antisymm a_1 a_2
