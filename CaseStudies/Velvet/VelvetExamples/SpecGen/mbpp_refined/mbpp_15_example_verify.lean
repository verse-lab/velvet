import Lean
import Mathlib.Tactic

-- Helper Functions

def isSegment (seg : List Char) : Prop :=
  ∃ c rest,
    seg = c :: rest ∧
    c.isLower ∧
    ∀ x ∈ rest, ¬ x.isLower

-- Postcondition clauses
def ensures1 (str : List Char) (result : List (List Char)) :=
  ∀ lst ∈ result, isSegment lst
def ensures2 (str : List Char) (result : List (List Char)) :=
  ∃ pre : List Char,
    (∀ x ∈ pre, ¬ x.isLower) ∧
    str = result.foldl (fun acc x => acc ++ x) pre

def precondition (str: List Char) :=
  True

def postcondition (str: List Char) (result: List (List Char)) :=
  ensures1 str result ∧ ensures2 str result

-- Test Cases
def test1_str : List Char := ['A', 'b', 'C', 'd']

def test1_Expected : List (List Char) := [['b', 'C'], ['d']]

def test2_str : List Char := []

def test2_Expected : List (List Char) := []

def test4_str : List Char := ['a', 'b', 'c', 'd']

def test4_Expected : List (List Char) := [['a'], ['b'], ['c'], ['d']]

def test5_str : List Char := ['a', 'B', 'C', 'd', 'E']

def test5_Expected : List (List Char) := [['a', 'B', 'C'], ['d', 'E']]

def test9_str : List Char := ['X', 'y', 'Z', 'a', 'B', 'c', 'D', 'E']

def test9_Expected : List (List Char) := [['y', 'Z'], ['a', 'B'], ['c', 'D', 'E']]

def test10_str : List Char := ['A', 'b', 'c', 'd', 'E']

def test10_Expected : List (List Char) := [['b'], ['c'], ['d', 'E']]

-------------------------------
-- Verifications
-------------------------------

-- test1
lemma test1_precondition :
  precondition test1_str := by
  trivial

lemma test1_postcondition :
  postcondition test1_str test1_Expected := by
  simp [postcondition, ensures1, ensures2, test1_Expected, test1_str, isSegment]
  use ['A']
  trivial

-- test2
lemma test2_precondition :
  precondition test2_str := by
  -- The precondition is trivially true since any string satisfies the condition.
  apply trivial

lemma test2_postcondition :
  postcondition test2_str test2_Expected := by
  simp [postcondition, ensures1, ensures2, test2_Expected, test2_str]

-- test4
lemma test4_precondition :
  precondition test4_str := by
  -- The precondition is trivially satisfied since `precondition` is defined as `True`.
  simp [precondition]

lemma test4_postcondition :
  postcondition test4_str test4_Expected := by
  simp [postcondition, ensures1, ensures2, test4_Expected, test4_str, isSegment]

-- test5
lemma test5_precondition :
  precondition test5_str := by
  -- The precondition is trivially true.
  trivial

lemma test5_postcondition :
  postcondition test5_str test5_Expected := by
  simp [postcondition, ensures1, ensures2, test5_Expected, test5_str, isSegment]

-- test9
lemma test9_precondition :
  precondition test9_str := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test9_postcondition :
  postcondition test9_str test9_Expected := by
  simp [postcondition, ensures1, ensures2, test9_Expected, test9_str, isSegment]
  use ['X']
  trivial


-- test10
lemma test10_precondition :
  precondition test10_str := by
  -- The precondition is trivially true since it is defined as True.
  simp [precondition]

lemma test10_postcondition :
  postcondition test10_str test10_Expected := by
  simp [postcondition, ensures1, ensures2, test10_Expected, test10_str, isSegment]
  use ['A']
  trivial

-----------------------------
-- Uniqueness Verification --
-----------------------------
noncomputable section AristotleLemmas

/-
Defines `join_segs` as the flattening of a list of segments using `foldl`, and proves that `foldl` with an accumulator `pre` is equivalent to `pre` appended to `join_segs`.
-/
def join_segs (l : List (List Char)) : List Char := l.foldl (fun acc x => acc ++ x) []

lemma foldl_eq_pre_append_join_segs (pre : List Char) (l : List (List Char)) :
  l.foldl (fun acc x => acc ++ x) pre = pre ++ join_segs l := by
    unfold join_segs;
    induction l using List.reverseRecOn <;> aesop

/-
`join_segs` of a cons list is the head appended to `join_segs` of the tail.
-/
lemma join_segs_cons (x : List Char) (xs : List (List Char)) :
  join_segs (x :: xs) = x ++ join_segs xs := by
    -- Unfold `join_segs`. It becomes `foldl ... ([] ++ x) xs` which is `foldl ... x xs`. By `foldl_eq_pre_append_join_segs` with `pre = x`, this is `x ++ join_segs xs`.
    exact foldl_eq_pre_append_join_segs x xs

/-
A segment is not empty because it consists of a head character and a tail.
-/
lemma segment_nonempty (s : List Char) :
  isSegment s → s ≠ [] := by
    rintro ⟨ c, rest, rfl, hc, hrest ⟩ ; aesop

/-
The head of a segment is a lowercase character.
-/
lemma segment_head_lower (s : List Char) :
  isSegment s → s.head!.isLower := by
    unfold isSegment;
    aesop

/-
The tail of a segment contains no lowercase characters.
-/
lemma segment_tail_not_lower (s : List Char) :
  isSegment s → ∀ c ∈ s.tail, ¬ c.isLower := by
    unfold isSegment; aesop;

/-
If a list of segments is non-empty, the joined string starts with a lowercase character.
-/
lemma join_segs_starts_lower (l : List (List Char)) :
  (∀ s ∈ l, isSegment s) → l ≠ [] → (join_segs l).head!.isLower := by
    intro h1 h2;
    induction' l using List.reverseRecOn with l ih;
    · contradiction;
    · by_cases hl : l = [] <;> simp_all +decide [ join_segs ];
      · exact?;
      · cases h : List.foldl ( fun acc x => acc ++ x ) [] l <;> aesop

/-
The prefix of non-lowercase characters is uniquely determined by the string.
-/
lemma unique_pre_aux (str : List Char) (pre : List Char) (l : List (List Char)) :
  (∀ x ∈ pre, ¬ x.isLower) →
  (∀ s ∈ l, isSegment s) →
  str = pre ++ join_segs l →
  pre = str.takeWhile (fun c => ¬ c.isLower) := by
    intros h1 h2 h3;
    -- By definition of `join_segs`, we know that `join_segs l` starts with a lowercase character if `l` is non-empty.
    by_cases hl : l = [];
    · -- Since `l` is empty, `join_segs l` is the empty list. Therefore, `str = pre ++ [] = pre`.
      simp [hl, h3];
      -- Since `join_segs []` is the empty list, we have `pre ++ join_segs [] = pre`.
      simp [join_segs];
      rw [ List.takeWhile_eq_self_iff.mpr ] ; aesop;
    · have h_join_lower : (join_segs l).head!.isLower := by
        exact?;
      rcases l' : join_segs l with ( _ | ⟨ c, l' ⟩ ) <;> aesop

/-
If two segments are prefixes of the same string, and the remainders either are empty or start with a lowercase character, then the segments are identical.
-/
lemma unique_first_segment (s1 s2 : List Char) (r1 r2 : List Char) :
  isSegment s1 →
  isSegment s2 →
  s1 ++ r1 = s2 ++ r2 →
  (r1 = [] ∨ r1.head!.isLower) →
  (r2 = [] ∨ r2.head!.isLower) →
  s1 = s2 := by
    revert s1 s2 r1 r2;
    intro s1 s2 r1 r2 hs1 hs2 h_eq hr1 hr2;
    rcases hs1 with ⟨ c1, rest1, rfl, hc1, hrest1 ⟩ ; rcases hs2 with ⟨ c2, rest2, rfl, hc2, hrest2 ⟩ ; simp_all +decide ;
    induction' rest1 with x rest1 ih generalizing rest2 <;> induction' rest2 with y rest2 ih' <;> aesop

/-
The decomposition of a string into segments is unique.
-/
lemma unique_segments (l1 l2 : List (List Char)) :
  (∀ s ∈ l1, isSegment s) →
  (∀ s ∈ l2, isSegment s) →
  join_segs l1 = join_segs l2 →
  l1 = l2 := by
    intro h1 h2;
    induction' l1 with s1 rs1 ih generalizing l2 <;> induction' l2 with s2 rs2 ih' <;> intro h3 <;> simp_all +decide [ join_segs_cons ];
    · rcases s2 with ( _ | ⟨ c, _ | ⟨ d, s2 ⟩ ⟩ ) <;> simp_all +decide [ join_segs ];
      cases h2 ; aesop;
    · cases s1 <;> simp_all +decide [ join_segs ];
      cases h1.1 ; aesop;
    · have h_unique_first_segment : s1 = s2 := by
        apply unique_first_segment s1 s2 (join_segs rs1) (join_segs rs2) h1.1 h2.1 h3;
        · by_cases h : rs1 = [] <;> simp_all +decide [ join_segs ];
          exact Or.inr ( join_segs_starts_lower rs1 h1.2 h );
        · by_cases h4 : rs2 = [];
          · aesop;
          · exact Or.inr ( join_segs_starts_lower rs2 h2.2 ( by aesop ) );
      aesop

end AristotleLemmas

lemma uniqueness (str: List Char):
  precondition str →
  (∀ ret1 ret2,
    postcondition str ret1 →
    postcondition str ret2 →
    ret1 = ret2) := by
  -- By definition of postcondition, if both ret1 and ret2 satisfy the postcondition, then they must both be equal to the buildSegments of the lowercase indices.
  intros h_pre ret1 ret2 h_ret1 h_ret2
  obtain ⟨ pre1, hpre1, hret1 ⟩ := h_ret1.2;
  have hpre2 : ∀ x ∈ pre1, ¬x.isLower = Bool.true := by
    assumption;
  have hret1' : str = pre1 ++ join_segs ret1 := by
    exact hret1.trans ( foldl_eq_pre_append_join_segs pre1 ret1 )
  have hret2' : str = (str.takeWhile (fun c => ¬ c.isLower)) ++ join_segs ret2 := by
    obtain ⟨ pre2, hpre2, hret2 ⟩ := h_ret2.2;
    have hret2' : str = pre2 ++ join_segs ret2 := by
      exact hret2.trans ( foldl_eq_pre_append_join_segs _ _ );
    have hpre2_eq : pre2 = str.takeWhile (fun c => ¬ c.isLower) := by
      apply unique_pre_aux;
      exacts [ hpre2, fun s hs => h_ret2.1 s hs, hret2' ];
    exact hpre2_eq ▸ hret2'
  have hpre1_eq : pre1 = str.takeWhile (fun c => ¬ c.isLower) := by
    apply unique_pre_aux;
    exacts [ hpre2, fun s hs => h_ret1.1 s hs, hret1' ];
  norm_num [ hpre1_eq ] at *;
  exact unique_segments ret1 ret2 h_ret1.1 h_ret2.1 ( by simpa using hret1'.symm.trans hret2' )
