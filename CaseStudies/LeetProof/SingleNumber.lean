module

public import Velvet
public meta import Velvet
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Nat.Init

/-!
## Program description

Given a non-empty array of integers `nums`, every element appears exactly twice
except for one element which appears only once. Find that single one.

The program is expected to run in O(n) time and O(1) extra space.
-/

namespace SingleNumber

section Specs

public def occursOnce (nums : Array Int) (x : Int) : Prop :=
  nums.count x = 1

public def occursTwice (nums : Array Int) (x : Int) : Prop :=
  nums.count x = 2

public def precondition (nums : Array Int) : Prop :=
  nums.size > 0 ∧
  (∃ s : Int,
    s ∈ nums ∧
    occursOnce nums s ∧
    (∀ y : Int, y ∈ nums → y ≠ s → occursTwice nums y))

public def postcondition (nums : Array Int) (result : Int) : Prop :=
  result ∈ nums ∧
  occursOnce nums result ∧
  (∀ y : Int, y ∈ nums → occursOnce nums y → y = result)

end Specs

section Implementation

public def encode (z : Int) : Nat :=
  if 0 ≤ z then 2 * z.toNat else 2 * ((-z).toNat - 1) + 1

public def decode (acc : Nat) : Int :=
  if acc % 2 = 0 then Int.ofNat (acc / 2) else Int.negSucc (acc / 2)

public def xorGo (nums : Array Int) (i : Nat) (acc : Nat) : Nat :=
  if i < nums.size then
    xorGo nums (i + 1) (Nat.xor acc (encode nums[i]!))
  else
    acc
termination_by nums.size - i

method singleNumber (nums : Array Int)
  returns (result : Int)
  requires valid: precondition nums
  ensures is_single: postcondition nums result
do
  let mut i : Nat := 0
  let mut acc : Nat := 0
  while scanning: i < nums.size
    invariant bounds: i ≤ nums.size
    invariant continuation: xorGo nums i acc = xorGo nums 0 0
    decreasing remaining: nums.size - i
    done_with done: i = nums.size
  do
    let z := nums[i]!
    let code := encode z
    acc := Nat.xor acc code
    i := i + 1
  return decode acc

end Implementation

section Proof

theorem decode_encode (z : Int) : decode (encode z) = z := by
  cases z with
  | ofNat n =>
    simp [encode, decode]
  | negSucc n =>
    have hmod : (2 * n + 1) % 2 = 1 := by omega
    have hdiv : (2 * n + 1) / 2 = n := by omega
    simp [encode, decode, hmod, hdiv]

public def xorStep (a : Nat) (z : Int) : Nat := Nat.xor a (encode z)

theorem xorGo_eq_drop_foldl (nums : Array Int) (i : Nat) (acc : Nat) :
    xorGo nums i acc = (nums.toList.drop i).foldl xorStep acc := by
  fun_induction xorGo nums i acc
  case case1 i a h ih =>
    have hdrop : nums.toList.drop i = nums[i]! :: nums.toList.drop (i + 1) := by
      have hd := List.drop_eq_getElem_cons (l := nums.toList) (i := i) (by simpa using h)
      rw [getElem!_pos nums i h]
      exact hd
    rw [ih, hdrop]
    rfl
  case case2 i a h =>
    have hlen : nums.toList.length ≤ i := by simpa using (Nat.le_of_not_gt h)
    simp [List.drop_eq_nil_iff.mpr hlen]

theorem xorGo_zero (nums : Array Int) :
    xorGo nums 0 0 = nums.toList.foldl xorStep 0 := by
  have h := xorGo_eq_drop_foldl nums 0 0
  simpa using h

instance : RightCommutative xorStep where
  right_comm a b c := by
    unfold xorStep
    calc
      Nat.xor (Nat.xor a (encode b)) (encode c)
          = Nat.xor a (Nat.xor (encode b) (encode c)) := by simp [Nat.xor_assoc]
      _ = Nat.xor a (Nat.xor (encode c) (encode b)) := by simp [Nat.xor_comm]
      _ = Nat.xor (Nat.xor a (encode c)) (encode b) := by simp [Nat.xor_assoc]

theorem length_erase_lt_of_mem {a : Int} {l : List Int} (ha : a ∈ l) :
    (l.erase a).length < l.length := by
  induction l with
  | nil => simp at ha
  | cons b tl ih =>
    simp only [List.mem_cons] at ha
    cases ha with
    | inl hba =>
      subst hba
      simp
    | inr hmem =>
      by_cases hba : b = a
      · subst hba
        simp
      · have : (tl.erase a).length < tl.length := ih hmem
        simp [hba, Nat.succ_lt_succ this]

theorem foldl_xor_init (l : List Int) (init : Nat) :
    l.foldl xorStep init = Nat.xor init (l.foldl xorStep 0) := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    have h_init : xs.foldl xorStep (Nat.xor init (encode x)) =
        Nat.xor (Nat.xor init (encode x)) (xs.foldl xorStep 0) :=
      ih (init := Nat.xor init (encode x))
    have h_enc : xs.foldl xorStep (encode x) =
        Nat.xor (encode x) (xs.foldl xorStep 0) :=
      ih (init := encode x)
    calc
      List.foldl xorStep init (x :: xs)
          = List.foldl xorStep (Nat.xor init (encode x)) xs := by
              simp [List.foldl, xorStep]
      _   = Nat.xor (Nat.xor init (encode x)) (List.foldl xorStep 0 xs) := h_init
      _   = Nat.xor init (Nat.xor (encode x) (List.foldl xorStep 0 xs)) := by
              simp [Nat.xor_assoc]
      _   = Nat.xor init (List.foldl xorStep (encode x) xs) := by
              simp [h_enc]
      _   = Nat.xor init (List.foldl xorStep 0 (x :: xs)) := by
              simp [List.foldl, xorStep, Nat.zero_xor]

theorem foldl_allTwice_len (n : Nat) :
    ∀ (l : List Int), l.length = n → (∀ y, y ∈ l → l.count y = 2) →
      l.foldl xorStep 0 = 0 := by
  induction n using Nat.strong_induction_on with
  | _ k ih =>
    intro l hlen hall
    cases l with
    | nil => simp
    | cons x xs =>
      have hx_count : (x :: xs).count x = 2 := hall x (by simp)
      have hxs_count : xs.count x = 1 := by
        have : xs.count x + 1 = 2 := by
          simpa [List.count_cons] using hx_count
        omega
      have hx_mem : x ∈ xs := by
        by_contra hn
        have : xs.count x = 0 := (List.count_eq_zero).2 hn
        simp [hxs_count] at this

      let rest : List Int := xs.erase x

      have p1 : List.Perm xs (x :: rest) := by
        simpa [rest] using (List.perm_cons_erase hx_mem)
      have p : List.Perm (x :: xs) (x :: x :: rest) := List.Perm.cons x p1

      have hperm : (x :: xs).foldl xorStep 0 = (x :: x :: rest).foldl xorStep 0 := by
        simpa using (List.Perm.foldl_eq (f := xorStep) p 0)

      have hcancel : (x :: x :: rest).foldl xorStep 0 = rest.foldl xorStep 0 := by
        simp [List.foldl, xorStep, Nat.zero_xor, Nat.xor_self]

      have hall_rest : ∀ y, y ∈ rest → rest.count y = 2 := by
        intro y hy
        have hy_xs : y ∈ xs := List.mem_of_mem_erase (by simpa [rest] using hy)
        have hy_ne_x : y ≠ x := by
          intro hyx
          subst y
          have hcount0 : rest.count x = 0 := by
            simp [rest, hxs_count, List.count_erase_self]
          have hnot : x ∉ rest := (List.count_eq_zero).1 hcount0
          exact hnot (by simpa using hy)
        have hy_ne_x' : x ≠ y := by
          intro hxy; exact hy_ne_x hxy.symm
        have hy_count_l : (x :: xs).count y = 2 := hall y (by simp [hy_xs])
        have hy_count_xs : xs.count y = 2 := by
          simpa [List.count_cons, hy_ne_x'] using hy_count_l
        simpa [rest, List.count_erase_of_ne hy_ne_x] using hy_count_xs

      have hlen_rest : rest.length < k := by
        have hrest : rest.length < xs.length := length_erase_lt_of_mem hx_mem
        simp only [List.length_cons] at hlen
        omega

      have ih_rest : rest.foldl xorStep 0 = 0 :=
        ih rest.length hlen_rest rest rfl hall_rest

      calc
        (x :: xs).foldl xorStep 0 = (x :: x :: rest).foldl xorStep 0 := hperm
        _ = rest.foldl xorStep 0 := hcancel
        _ = 0 := ih_rest

theorem foldl_allTwice (l : List Int) (hall : ∀ y, y ∈ l → l.count y = 2) :
    l.foldl xorStep 0 = 0 :=
  foldl_allTwice_len l.length l rfl hall

theorem foldl_unique_len (n : Nat) (s : Int) :
    ∀ (l : List Int), l.length = n → l.count s = 1 →
      (∀ y, y ∈ l → y ≠ s → l.count y = 2) →
      l.foldl xorStep 0 = encode s := by
  induction n using Nat.strong_induction_on with
  | _ k ih =>
    intro l hlen hs htw
    cases l with
    | nil =>
      simp at hs
    | cons x xs =>
      by_cases hx : x = s
      · subst s
        have hs_tail0 : xs.count x = 0 := by
          simp at hs
          omega
        have hall_tail : ∀ y, y ∈ xs → xs.count y = 2 := by
          intro y hy
          have hy_ne_x : y ≠ x := by
            intro hyx
            subst y
            have hnot : x ∉ xs := (List.count_eq_zero).1 hs_tail0
            exact hnot hy
          have hy_count : (x :: xs).count y = 2 := htw y (by simp [hy]) hy_ne_x
          have hy_ne_x' : x ≠ y := by
            intro hxy; exact hy_ne_x hxy.symm
          simpa [List.count_cons, hy_ne_x'] using hy_count
        have htail0 : xs.foldl xorStep 0 = 0 := foldl_allTwice xs hall_tail
        have hfold_enc : xs.foldl xorStep (encode x) = encode x := by
          have := foldl_xor_init xs (encode x)
          simpa [htail0, Nat.xor_zero] using this
        simpa [List.foldl, xorStep, Nat.zero_xor] using hfold_enc
      ·
        have hx_count : (x :: xs).count x = 2 := htw x (by simp) (by simp [hx])
        have hxs_count : xs.count x = 1 := by
          have : xs.count x + 1 = 2 := by
            have := hx_count
            simp at this
            omega
          omega
        have hx_mem : x ∈ xs := by
          by_contra hn
          have : xs.count x = 0 := (List.count_eq_zero).2 hn
          simp [hxs_count] at this

        let rest : List Int := xs.erase x

        have p1 : List.Perm xs (x :: rest) := by
          simpa [rest] using (List.perm_cons_erase hx_mem)
        have p : List.Perm (x :: xs) (x :: x :: rest) := List.Perm.cons x p1

        have hperm : (x :: xs).foldl xorStep 0 = (x :: x :: rest).foldl xorStep 0 := by
          simpa using (List.Perm.foldl_eq (f := xorStep) p 0)

        have hcancel : (x :: x :: rest).foldl xorStep 0 = rest.foldl xorStep 0 := by
          simp [List.foldl, xorStep, Nat.zero_xor, Nat.xor_self]

        have hs_rest : rest.count s = 1 := by
          have hs_xs : xs.count s = 1 := by
            simpa [List.count_cons, hx] using hs
          have hs_ne_x : s ≠ x := by
            intro h; exact hx h.symm
          have : rest.count s = xs.count s := by
            simp [rest, List.count_erase_of_ne hs_ne_x]
          simp [this, hs_xs]

        have htw_rest : ∀ y, y ∈ rest → y ≠ s → rest.count y = 2 := by
          intro y hy hy_ne_s
          have hy_xs : y ∈ xs := List.mem_of_mem_erase (by simpa [rest] using hy)
          have hy_ne_x : y ≠ x := by
            intro hyx
            subst y
            have hcount0 : rest.count x = 0 := by
              simp [rest, hxs_count, List.count_erase_self]
            have hnot : x ∉ rest := (List.count_eq_zero).1 hcount0
            exact hnot (by simpa using hy)
          have hy_ne_x' : x ≠ y := by
            intro hxy; exact hy_ne_x hxy.symm
          have hy_count_l : (x :: xs).count y = 2 := htw y (by simp [hy_xs]) hy_ne_s
          have hy_count_xs : xs.count y = 2 := by
            simpa [List.count_cons, hy_ne_x'] using hy_count_l
          simpa [rest, List.count_erase_of_ne hy_ne_x] using hy_count_xs

        have hlen_rest : rest.length < k := by
          have hrest : rest.length < xs.length := length_erase_lt_of_mem hx_mem
          simp only [List.length_cons] at hlen
          omega

        have ih_rest : rest.foldl xorStep 0 = encode s :=
          ih rest.length hlen_rest rest rfl hs_rest htw_rest

        calc
          (x :: xs).foldl xorStep 0 = (x :: x :: rest).foldl xorStep 0 := hperm
          _ = rest.foldl xorStep 0 := hcancel
          _ = encode s := ih_rest

theorem foldl_unique (l : List Int) (s : Int) (hs : l.count s = 1)
    (htw : ∀ y, y ∈ l → y ≠ s → l.count y = 2) :
    l.foldl xorStep 0 = encode s :=
  foldl_unique_len l.length s l rfl hs htw

theorem xorGo_correct (nums : Array Int) (s : Int)
    (hs_count : occursOnce nums s)
    (htwice : ∀ y ∈ nums, y ≠ s → occursTwice nums y) :
    xorGo nums 0 0 = encode s := by
  have hs_countL : nums.toList.count s = 1 := by
    simpa [Array.count_toList, occursOnce] using hs_count
  have htwiceL : ∀ y, y ∈ nums.toList → y ≠ s → nums.toList.count y = 2 := by
    intro y hy hy_ne
    have hyA : y ∈ nums := by simpa using hy
    have := htwice y hyA hy_ne
    simpa [Array.count_toList, occursTwice] using this
  rw [xorGo_zero]
  exact foldl_unique nums.toList s hs_countL htwiceL

theorem singleNumber_correct (nums : Array Int) (hpre : precondition nums) :
    postcondition nums (decode (xorGo nums 0 0)) := by
  rcases hpre with ⟨_hsize, ⟨s, hs_mem, hs_once, htwice⟩⟩
  have hxor := xorGo_correct nums s hs_once htwice
  rw [hxor, decode_encode]
  refine ⟨hs_mem, hs_once, ?_⟩
  intro y hy_mem hy_once
  have hy_count : nums.count y = 1 := hy_once
  by_contra hne
  have hy_two : occursTwice nums y := htwice y hy_mem hne
  have h2 : nums.count y = 2 := hy_two
  omega

prove_correct singleNumber by
  velvet_vcgen [singleNumber, postcondition] with try finish
  case continuation =>
    rename_i nums
    rw [getElem!_pos nums i scanning]
    rw [xorGo.eq_def] at continuation
    simp [scanning] at continuation
    exact continuation
  case is_single =>
    rw [xorGo.eq_def] at continuation
    simp [done] at continuation
    rw [continuation]
    exact singleNumber_correct _ valid

end Proof

end SingleNumber
