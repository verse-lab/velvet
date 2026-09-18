module

public import Velvet
public meta import Velvet
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Int.Order.Basic

/-!
## Program description

Rearrange an even-length integer array with equal numbers of positive and
negative elements so that signs alternate starting with a positive, while
preserving the relative order of elements within each sign.

The program is expected to run in O(n) time and O(n) extra space.
-/

namespace RearrangeArrayElementsBySign

section Specs

public def isPosB (x : Int) : Bool := decide (x > 0)

public def isNegB (x : Int) : Bool := decide (x < 0)

public def countPos (nums : Array Int) : Nat := nums.countP isPosB

public def countNeg (nums : Array Int) : Nat := nums.countP isNegB

public def allNonZero (nums : Array Int) : Prop :=
  ∀ (i : Nat), i < nums.size → nums[i]! ≠ 0

public def alternatesStartingPos (arr : Array Int) : Prop :=
  ∀ (i : Nat), i < arr.size →
    ((i % 2 = 0) → arr[i]! > 0) ∧
    ((i % 2 = 1) → arr[i]! < 0)

public def stableBySign (nums : Array Int) (result : Array Int) : Prop :=
  result.filter isPosB = nums.filter isPosB ∧
  result.filter isNegB = nums.filter isNegB

public def precondition (nums : Array Int) : Prop :=
  nums.size % 2 = 0 ∧
  allNonZero nums ∧
  countPos nums = nums.size / 2 ∧
  countNeg nums = nums.size / 2

public def postcondition (nums : Array Int) (result : Array Int) : Prop :=
  result.size = nums.size ∧
  result.Perm nums ∧
  alternatesStartingPos result ∧
  (result.size > 0 → result[0]! > 0) ∧
  stableBySign nums result

end Specs

section Implementation

public def collectGo (nums : Array Int) (i : Nat) (pos neg : Array Int) : Array Int × Array Int :=
  if i < nums.size then
    let x := nums[i]!
    if x > 0 then
      collectGo nums (i + 1) (pos.push x) neg
    else
      collectGo nums (i + 1) pos (neg.push x)
  else (pos, neg)
termination_by nums.size - i

public def interleaveGo (pos neg : Array Int) (i : Nat) (n : Nat) (acc : Array Int) : Array Int :=
  if i < n then
    interleaveGo pos neg (i + 1) n ((acc.push pos[i]!).push neg[i]!)
  else acc
termination_by n - i

public def rearrange (nums : Array Int) : Array Int :=
  let (pos, neg) := collectGo nums 0 #[] #[]
  interleaveGo pos neg 0 (nums.size / 2) #[]

method rearrangeArray (nums : Array Int)
  returns (result : Array Int)
  requires valid: precondition nums
  ensures rearranged: postcondition nums result
do
  let mut pos : Array Int := #[]
  let mut neg : Array Int := #[]
  let mut i : Nat := 0
  while' collecting: i < nums.size
    invariant continuation: collectGo nums i pos neg = collectGo nums 0 #[] #[]
    decreasing remaining: nums.size - i
  do
    let x := nums[i]!
    if pos_elem: x > 0 then
      pos := pos.push x
    else
      neg := neg.push x
    i := i + 1
  let mut res : Array Int := #[]
  let mut j : Nat := 0
  let n := nums.size / 2
  while' interleaving: j < n
    invariant continuation: interleaveGo pos neg j n res = interleaveGo pos neg 0 n #[]
    decreasing remaining: n - j
  do
    res := (res.push pos[j]!).push neg[j]!
    j := j + 1
  return res

end Implementation

section Proof

public def interleaveLists : List Int → List Int → List Int
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => a :: b :: interleaveLists as bs

theorem interleaveLists_length (p q : List Int) (h : p.length = q.length) :
    (interleaveLists p q).length = 2 * p.length := by
  induction p generalizing q with
  | nil =>
      cases q with
      | nil => rfl
      | cons _ _ => contradiction
  | cons a as ih =>
      cases q with
      | nil => contradiction
      | cons b bs =>
          simp only [List.length_cons] at h
          have h' : as.length = bs.length := by omega
          simp [interleaveLists, ih bs h']
          omega

theorem interleaveLists_filter_pos (p q : List Int) (hp : ∀ x ∈ p, 0 < x) (hq : ∀ x ∈ q, x < 0) (h : p.length = q.length) :
    (interleaveLists p q).filter isPosB = p := by
  induction p generalizing q with
  | nil => rfl
  | cons a as ih =>
      cases q with
      | nil => contradiction
      | cons b bs =>
          have ha_pos : isPosB a = true := by
            simp [isPosB, hp a (by simp)]
          have hb_pos : isPosB b = false := by
            have hb_neg : b < 0 := hq b (by simp)
            have : ¬ b > 0 := not_lt_of_ge (le_of_lt hb_neg)
            simp [isPosB, this]
          have h_as : ∀ x ∈ as, 0 < x := fun x hx => hp x (List.mem_cons_of_mem a hx)
          have h_bs : ∀ x ∈ bs, x < 0 := fun x hx => hq x (List.mem_cons_of_mem b hx)
          simp only [List.length_cons] at h
          have h_len : as.length = bs.length := by omega
          simp [interleaveLists, ha_pos, hb_pos, ih bs h_as h_bs h_len]

theorem interleaveLists_filter_neg (p q : List Int) (hp : ∀ x ∈ p, 0 < x) (hq : ∀ x ∈ q, x < 0) (h : p.length = q.length) :
    (interleaveLists p q).filter isNegB = q := by
  induction p generalizing q with
  | nil =>
      cases q with
      | nil => rfl
      | cons _ _ => contradiction
  | cons a as ih =>
      cases q with
      | nil => contradiction
      | cons b bs =>
          have ha_neg : isNegB a = false := by
            have ha_pos : a > 0 := hp a (by simp)
            have : ¬ a < 0 := not_lt_of_ge (le_of_lt ha_pos)
            simp [isNegB, this]
          have hb_neg : isNegB b = true := by
            simp [isNegB, hq b (by simp)]
          have h_as : ∀ x ∈ as, 0 < x := fun x hx => hp x (List.mem_cons_of_mem a hx)
          have h_bs : ∀ x ∈ bs, x < 0 := fun x hx => hq x (List.mem_cons_of_mem b hx)
          simp only [List.length_cons] at h
          have h_len : as.length = bs.length := by omega
          simp [interleaveLists, ha_neg, hb_neg, ih bs h_as h_bs h_len]

theorem interleaveLists_perm (p q : List Int) (h : p.length = q.length) :
    (interleaveLists p q).Perm (p ++ q) := by
  induction p generalizing q with
  | nil =>
      cases q with
      | nil => exact List.Perm.refl []
      | cons _ _ => contradiction
  | cons a as ih =>
      cases q with
      | nil => contradiction
      | cons b bs =>
          simp only [List.length_cons] at h
          have h' : as.length = bs.length := by omega
          have ih' := ih bs h'
          simp only [interleaveLists, List.cons_append]
          have h_perm1 : (a :: b :: interleaveLists as bs).Perm (a :: b :: (as ++ bs)) :=
            List.Perm.cons a (List.Perm.cons b ih')
          have h_perm2 : (b :: (as ++ bs)).Perm (as ++ b :: bs) :=
            List.perm_middle.symm
          exact h_perm1.trans (List.Perm.cons a h_perm2)

theorem list_perm_filter_pos_neg (l : List Int) (hnz : ∀ x ∈ l, x ≠ 0) :
    (l.filter isPosB ++ l.filter isNegB).Perm l := by
  induction l with
  | nil => exact List.Perm.refl []
  | cons x xs ih =>
      have hx_nz : x ≠ 0 := hnz x (by simp)
      have hxs_nz : ∀ y ∈ xs, y ≠ 0 := fun y hy => hnz y (List.mem_cons_of_mem x hy)
      have ih' := ih hxs_nz
      rcases lt_trichotomy x 0 with hneg | heq | hpos
      · have hpos_b : isPosB x = false := by
          have : ¬ x > 0 := not_lt_of_ge (le_of_lt hneg)
          simp [isPosB, this]
        have hneg_b : isNegB x = true := by simp [isNegB, hneg]
        simp only [List.filter_cons, hpos_b, Bool.false_eq_true, ↓reduceIte, hneg_b]
        have hmid : (xs.filter isPosB ++ x :: xs.filter isNegB).Perm (x :: (xs.filter isPosB ++ xs.filter isNegB)) :=
          List.perm_middle
        exact hmid.trans (List.Perm.cons x ih')
      · contradiction
      · have hpos_b : isPosB x = true := by simp [isPosB, hpos]
        have hneg_b : isNegB x = false := by
          have : ¬ x < 0 := not_lt_of_ge (le_of_lt hpos)
          simp [isNegB, this]
        simp only [List.filter_cons, hpos_b, ↓reduceIte, hneg_b, Bool.false_eq_true, List.cons_append]
        exact List.Perm.cons x ih'

theorem interleaveLists_getElem? (p q : List Int) (h : p.length = q.length) (k : Nat) (hk : k < 2 * p.length) :
    ((k % 2 = 0) → (interleaveLists p q)[k]? = p[k / 2]?) ∧
    ((k % 2 = 1) → (interleaveLists p q)[k]? = q[k / 2]?) := by
  induction p generalizing q k with
  | nil =>
      cases q with
      | nil => contradiction
      | cons _ _ => contradiction
  | cons a as ih =>
      cases q with
      | nil => contradiction
      | cons b bs =>
          simp only [List.length_cons] at h hk
          have h' : as.length = bs.length := by omega
          cases k with
          | zero =>
              simp [interleaveLists]
          | succ k =>
              cases k with
              | zero =>
                  simp [interleaveLists]
              | succ k =>
                  have hk' : k < 2 * as.length := by omega
                  have ih' := ih bs h' k hk'
                  have hmod : (k + 2) % 2 = k % 2 := by simp
                  have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
                  constructor
                  · intro h0
                    rw [hmod] at h0
                    have h_get := ih'.1 h0
                    simp [interleaveLists, hdiv, h_get]
                  · intro h1
                    rw [hmod] at h1
                    have h_get := ih'.2 h1
                    simp [interleaveLists, hdiv, h_get]

theorem interleaveGo_acc (pos neg : Array Int) (i n : Nat) (acc : Array Int) :
    (interleaveGo pos neg i n acc).toList =
      acc.toList ++ (interleaveGo pos neg i n #[]).toList := by
  induction h_rem : n - i using Nat.strong_induction_on generalizing i acc with
  | h m ih =>
      rw [interleaveGo.eq_def]
      by_cases hi : i < n
      · simp only [hi, ↓reduceIte]
        have hrec : n - (i + 1) < m := by omega
        have ih1 := ih (n - (i + 1)) hrec (i + 1) ((acc.push pos[i]!).push neg[i]!) rfl
        have ih2 := ih (n - (i + 1)) hrec (i + 1) ((#[].push pos[i]!).push neg[i]!) rfl
        rw [ih1]
        conv_rhs => rw [interleaveGo.eq_def]; simp only [hi, ↓reduceIte]; rw [ih2]
        simp
      · simp only [hi, ↓reduceIte]
        conv_rhs => rw [interleaveGo.eq_def]; simp only [hi, ↓reduceIte]
        simp

theorem interleaveGo_zero_toList (pos neg : Array Int) (n : Nat)
    (hpos : n ≤ pos.size) (hneg : n ≤ neg.size) :
    (interleaveGo pos neg 0 n #[]).toList =
      interleaveLists (pos.toList.take n) (neg.toList.take n) := by
  have h_gen : ∀ i, i ≤ n →
      (interleaveGo pos neg i n #[]).toList =
        interleaveLists ((pos.toList.take n).drop i) ((neg.toList.take n).drop i) := by
    intro i hi_le
    induction h_rem : n - i using Nat.strong_induction_on generalizing i with
    | h m ih =>
        rw [interleaveGo.eq_def]
        by_cases hi : i < n
        · simp only [hi, ↓reduceIte]
          have h_step : (interleaveGo pos neg (i + 1) n ((#[].push pos[i]!).push neg[i]!)).toList =
              pos[i]! :: neg[i]! :: (interleaveGo pos neg (i + 1) n #[]).toList := by
            have := interleaveGo_acc pos neg (i + 1) n ((#[].push pos[i]!).push neg[i]!)
            rw [this]
            rfl
          rw [h_step]
          have hrec : n - (i + 1) < m := by omega
          have ih' := ih (n - (i + 1)) hrec (i + 1) (by omega) rfl
          rw [ih']
          have hp_drop : (pos.toList.take n).drop i = pos[i]! :: (pos.toList.take n).drop (i + 1) := by
            have hi' : i < (pos.toList.take n).length := by
              simp [Nat.min_eq_left hpos, hi]
            have h_lt : i < pos.size := by omega
            have h_get : (pos.toList.take n)[i] = pos[i]! := by
              simp [List.getElem_take, h_lt]
            have h_drop_eq := List.drop_eq_getElem_cons hi'
            rw [h_get] at h_drop_eq
            exact h_drop_eq
          have hq_drop : (neg.toList.take n).drop i = neg[i]! :: (neg.toList.take n).drop (i + 1) := by
            have hi' : i < (neg.toList.take n).length := by
              simp [Nat.min_eq_left hneg, hi]
            have h_lt : i < neg.size := by omega
            have h_get : (neg.toList.take n)[i] = neg[i]! := by
              simp [List.getElem_take, h_lt]
            have h_drop_eq := List.drop_eq_getElem_cons hi'
            rw [h_get] at h_drop_eq
            exact h_drop_eq
          rw [hp_drop, hq_drop]
          simp [interleaveLists]
        · simp only [hi, ↓reduceIte]
          have hp_drop : (pos.toList.take n).drop i = [] :=
            List.drop_of_length_le (by simp [Nat.min_eq_left hpos]; omega)
          have hq_drop : (neg.toList.take n).drop i = [] :=
            List.drop_of_length_le (by simp [Nat.min_eq_left hneg]; omega)
          simp [hp_drop, hq_drop, interleaveLists]
  simpa using h_gen 0 (by omega)

theorem collectGo_toList (nums : Array Int) (hnz : allNonZero nums) (i : Nat) (pos neg : Array Int) :
    (collectGo nums i pos neg).1.toList = pos.toList ++ (nums.toList.drop i).filter isPosB ∧
    (collectGo nums i pos neg).2.toList = neg.toList ++ (nums.toList.drop i).filter isNegB := by
  induction h_rem : nums.size - i using Nat.strong_induction_on generalizing i pos neg with
  | h n ih =>
      rw [collectGo.eq_def]
      by_cases hi : i < nums.size
      · have hdrop : nums.toList.drop i = nums[i]! :: nums.toList.drop (i + 1) := by
          have hi' : i < nums.toList.length := by simpa using hi
          have h_get : nums.toList[i] = nums[i]! := (getElem!_pos nums i hi).symm
          have h_drop_eq := List.drop_eq_getElem_cons hi'
          rw [h_get] at h_drop_eq
          exact h_drop_eq
        have hrec : nums.size - (i + 1) < n := by omega
        by_cases hpos : nums[i]! > 0
        · simp only [hi, hpos, ↓reduceIte]
          have ih' := ih (nums.size - (i + 1)) hrec (i + 1) (pos.push nums[i]!) neg rfl
          have hpos_b : isPosB nums[i]! = true := by simp [isPosB, hpos]
          have hneg_b : isNegB nums[i]! = false := by
            have : ¬ nums[i]! < 0 := not_lt_of_ge (le_of_lt hpos)
            simp [isNegB, this]
          constructor
          · rw [ih'.1, hdrop]
            simp [hpos_b]
          · rw [ih'.2, hdrop]
            simp [hneg_b]
        · simp only [hi, hpos, ↓reduceIte]
          have ih' := ih (nums.size - (i + 1)) hrec (i + 1) pos (neg.push nums[i]!) rfl
          have hnz_i : nums[i]! ≠ 0 := hnz i hi
          have hneg : nums[i]! < 0 := by
            rcases lt_trichotomy nums[i]! 0 with h1 | h2 | h3
            · exact h1
            · contradiction
            · contradiction
          have hpos_b : isPosB nums[i]! = false := by
            have : ¬ nums[i]! > 0 := not_lt_of_ge (le_of_lt hneg)
            simp [isPosB, this]
          have hneg_b : isNegB nums[i]! = true := by simp [isNegB, hneg]
          constructor
          · rw [ih'.1, hdrop]
            simp [hpos_b]
          · rw [ih'.2, hdrop]
            simp [hneg_b]
      · simp only [hi, ↓reduceIte]
        have hdrop : nums.toList.drop i = [] := List.drop_of_length_le (by simpa using Nat.le_of_not_lt hi)
        simp [hdrop]

theorem rearrange_correct (nums : Array Int) (hpre : precondition nums) :
    postcondition nums (rearrange nums) := by
  rcases hpre with ⟨heven, hnz, hcount_pos, hcount_neg⟩
  have hpos_size : (nums.filter isPosB).size = nums.size / 2 := by
    simpa [countPos] using (Array.countP_eq_size_filter (p := isPosB) (xs := nums)).symm.trans hcount_pos
  have hneg_size : (nums.filter isNegB).size = nums.size / 2 := by
    simpa [countNeg] using (Array.countP_eq_size_filter (p := isNegB) (xs := nums)).symm.trans hcount_neg
  have hcollect := collectGo_toList nums hnz 0 #[] #[]
  simp only [List.drop_zero, List.nil_append] at hcollect
  have hpos_eq : (collectGo nums 0 #[] #[]).1 = nums.filter isPosB := by
    apply Array.ext'
    simp [hcollect.1]
  have hneg_eq : (collectGo nums 0 #[] #[]).2 = nums.filter isNegB := by
    apply Array.ext'
    simp [hcollect.2]
  have hcollect_pair : collectGo nums 0 #[] #[] = (nums.filter isPosB, nums.filter isNegB) :=
    Prod.ext hpos_eq hneg_eq
  unfold rearrange
  rw [hcollect_pair]
  dsimp
  have hpos_len : (nums.filter isPosB).toList.length = nums.size / 2 := by
    have : (nums.filter isPosB).toList.length = (nums.filter isPosB).size := rfl
    rw [this, hpos_size]
  have hneg_len : (nums.filter isNegB).toList.length = nums.size / 2 := by
    have : (nums.filter isNegB).toList.length = (nums.filter isNegB).size := rfl
    rw [this, hneg_size]
  have hinter := interleaveGo_zero_toList (nums.filter isPosB) (nums.filter isNegB) (nums.size / 2)
    (by simp [hpos_size]) (by simp [hneg_size])
  have hpos_take : (nums.filter isPosB).toList.take (nums.size / 2) = (nums.filter isPosB).toList := by
    rw [← hpos_len, List.take_length]
  have hneg_take : (nums.filter isNegB).toList.take (nums.size / 2) = (nums.filter isNegB).toList := by
    rw [← hneg_len, List.take_length]
  rw [hpos_take, hneg_take] at hinter
  let p := (nums.filter isPosB).toList
  let q := (nums.filter isNegB).toList
  have hp_len : p.length = nums.size / 2 := hpos_len
  have hq_len : q.length = nums.size / 2 := hneg_len
  have hpq_eq : p.length = q.length := by omega
  have hp_pos : ∀ x ∈ p, 0 < x := by
    intro x hx
    have hx' : x ∈ nums.toList.filter isPosB := by
      simpa [p, Array.toList_filter] using hx
    have hx'' := (List.mem_filter.1 hx').2
    simpa [isPosB] using hx''
  have hq_neg : ∀ x ∈ q, x < 0 := by
    intro x hx
    have hx' : x ∈ nums.toList.filter isNegB := by
      simpa [q, Array.toList_filter] using hx
    have hx'' := (List.mem_filter.1 hx').2
    simpa [isNegB] using hx''
  have hres_list : (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList =
      interleaveLists p q := hinter
  unfold postcondition
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- size
    have hlen : (interleaveLists p q).length = 2 * (nums.size / 2) := by
      rw [interleaveLists_length p q hpq_eq, hp_len]
    have : (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).size =
        (interleaveLists p q).length := by
      have : (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).size =
          (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList.length := rfl
      rw [this, hres_list]
    rw [this, hlen]
    omega
  · -- Perm
    rw [Array.perm_iff_toList_perm, hres_list]
    have hperm1 := interleaveLists_perm p q hpq_eq
    have hnz_list : ∀ x ∈ nums.toList, x ≠ 0 := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hi' : i < nums.size := by simpa using hi
      simpa [getElem!_pos nums i hi'] using hnz i hi'
    have hperm2 := list_perm_filter_pos_neg nums.toList hnz_list
    have hp_def : p = nums.toList.filter isPosB := Array.toList_filter
    have hq_def : q = nums.toList.filter isNegB := Array.toList_filter
    have hperm2' : (p ++ q).Perm nums.toList := by
      rw [hp_def, hq_def]
      exact hperm2
    exact hperm1.trans hperm2'
  · -- alternatesStartingPos
    unfold alternatesStartingPos
    intro k hk
    have hk_len : k < (interleaveLists p q).length := by
      have : (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).size =
          (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList.length := rfl
      rw [this, hres_list] at hk
      exact hk
    have hk_2p : k < 2 * p.length := by
      rw [interleaveLists_length p q hpq_eq] at hk_len
      exact hk_len
    have hget_elem := interleaveLists_getElem? p q hpq_eq k hk_2p
    constructor
    · intro hmod0
      have hk2_lt : k / 2 < p.length := by omega
      have hp_get : p[k / 2]? = some p[k / 2] := List.getElem?_eq_getElem hk2_lt
      have h_some : ((interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList)[k]? = some p[k / 2] := by
        rw [hres_list]
        exact (hget_elem.1 hmod0).trans hp_get
      have h_get : ((interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList)[k]? =
          some ((interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList[k]) :=
        List.getElem?_eq_getElem (by simpa using hk)
      rw [h_get] at h_some
      have h_val := Option.some.inj h_some
      have h1 : (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[])[k]! =
          (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList[k] := by
        rw [getElem!_pos _ _ (by simpa using hk)]
        rfl
      rw [h1, h_val]
      exact hp_pos p[k / 2] (List.getElem_mem hk2_lt)
    · intro hmod1
      have hk2_lt : k / 2 < q.length := by omega
      have hq_get : q[k / 2]? = some q[k / 2] := List.getElem?_eq_getElem hk2_lt
      have h_some : ((interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList)[k]? = some q[k / 2] := by
        rw [hres_list]
        exact (hget_elem.2 hmod1).trans hq_get
      have h_get : ((interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList)[k]? =
          some ((interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList[k]) :=
        List.getElem?_eq_getElem (by simpa using hk)
      rw [h_get] at h_some
      have h_val := Option.some.inj h_some
      have h1 : (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[])[k]! =
          (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList[k] := by
        rw [getElem!_pos _ _ (by simpa using hk)]
        rfl
      rw [h1, h_val]
      exact hq_neg q[k / 2] (List.getElem_mem hk2_lt)
  · -- starts positive
    intro hpos_sz
    have hk0_len : 0 < (interleaveLists p q).length := by
      have : (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).size =
          (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList.length := rfl
      rw [this, hres_list] at hpos_sz
      exact hpos_sz
    have hk0_2p : 0 < 2 * p.length := by
      rw [interleaveLists_length p q hpq_eq] at hk0_len
      exact hk0_len
    have hget_elem := (interleaveLists_getElem? p q hpq_eq 0 hk0_2p).1 (by simp)
    have hp0_lt : 0 < p.length := by omega
    have hp_get : p[0]? = some p[0] := List.getElem?_eq_getElem hp0_lt
    have h_some : ((interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList)[0]? = some p[0] := by
      rw [hres_list]
      exact hget_elem.trans hp_get
    have h_get : ((interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList)[0]? =
        some ((interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList[0]) :=
      List.getElem?_eq_getElem (by simpa using hpos_sz)
    rw [h_get] at h_some
    have h_val := Option.some.inj h_some
    have h1 : (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[])[0]! =
        (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[]).toList[0] := by
      rw [getElem!_pos _ _ (by simpa using hpos_sz)]
      rfl
    rw [h1, h_val]
    exact hp_pos p[0] (List.getElem_mem hp0_lt)
  · -- stableBySign
    unfold stableBySign
    constructor
    · apply Array.ext'
      have h1 : (Array.filter isPosB (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[])).toList =
          (interleaveLists p q).filter isPosB := by
        rw [Array.toList_filter, hres_list]
      have h2 := interleaveLists_filter_pos p q hp_pos hq_neg hpq_eq
      rw [h1, h2]
    · apply Array.ext'
      have h1 : (Array.filter isNegB (interleaveGo (nums.filter isPosB) (nums.filter isNegB) 0 (nums.size / 2) #[])).toList =
          (interleaveLists p q).filter isNegB := by
        rw [Array.toList_filter, hres_list]
      have h2 := interleaveLists_filter_neg p q hp_pos hq_neg hpq_eq
      rw [h1, h2]

prove_correct rearrangeArray by
  velvet_vcgen [rearrangeArray, postcondition] with try finish
  case rearranged =>
    rename_i nums
    rw [collectGo.eq_def (i := i)] at continuation
    simp only [h_done_with, ↓reduceIte] at continuation
    rw [interleaveGo.eq_def (i := j)] at continuation_1
    simp only [h_done_with_1, ↓reduceIte] at continuation_1
    have h_rearrange : res = rearrange nums := by
      unfold rearrange
      rw [← continuation]
      dsimp
      exact continuation_1
    rw [h_rearrange]
    exact rearrange_correct nums valid
  case continuation =>
    rw [interleaveGo.eq_def (i := j)] at continuation_1
    simp only [interleaving, ↓reduceIte] at continuation_1
    exact continuation_1
  case continuation =>
    rw [collectGo.eq_def (i := i)] at continuation
    simp only [collecting, pos_elem, ↓reduceIte] at continuation
    exact continuation
  case continuation =>
    rw [collectGo.eq_def (i := i)] at continuation
    simp only [collecting, pos_elem, ↓reduceIte] at continuation
    exact continuation


end Proof

end RearrangeArrayElementsBySign
