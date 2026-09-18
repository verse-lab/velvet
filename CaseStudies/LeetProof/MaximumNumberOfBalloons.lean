module

public import Velvet
public meta import Velvet
public import Mathlib.Tactic.Set

/-!
## Program description

Given a string `text`, return the maximum number of instances of the word
"balloon" that can be formed using the characters in `text`. You can use each
character in `text` at most once.

1. Input is a sequence of characters `text`.
2. A single instance of the word "balloon" requires the multiset of letters:
   'b' × 1, 'a' × 1, 'l' × 2, 'o' × 2, 'n' × 1.
3. Each character from `text` may be used at most once across all formed instances.
4. The output is the maximum natural number `k` such that `text` contains at
   least the required number of each character to form `k` instances.
5. If `text` lacks any required character, the maximum is 0.

The program is expected to run in O(n) time and O(1) extra space.
-/

namespace MaximumNumberOfBalloons

section Specs

public def charCount (text : List Char) (c : Char) : Nat :=
  text.count c

public def feasibleBalloons (text : List Char) (k : Nat) : Prop :=
  k ≤ charCount text 'b' ∧
  k ≤ charCount text 'a' ∧
  (2 * k) ≤ charCount text 'l' ∧
  (2 * k) ≤ charCount text 'o' ∧
  k ≤ charCount text 'n'

public def precondition (_text : List Char) : Prop :=
  True

public def postcondition (text : List Char) (result : Nat) : Prop :=
  feasibleBalloons text result ∧
  (∀ k : Nat, feasibleBalloons text k → k ≤ result)

end Specs

section Implementation

method maxNumberOfBalloons (text : List Char)
  returns (result : Nat)
  requires valid: precondition text
  ensures max_balloons: postcondition text result
do
  let mut rem : List Char := text
  let mut cb : Nat := 0
  let mut ca : Nat := 0
  let mut cl : Nat := 0
  let mut co : Nat := 0
  let mut cn : Nat := 0
  while scanning: rem ≠ []
    invariant count_b: cb + charCount rem 'b' = charCount text 'b'
    invariant count_a: ca + charCount rem 'a' = charCount text 'a'
    invariant count_l: cl + charCount rem 'l' = charCount text 'l'
    invariant count_o: co + charCount rem 'o' = charCount text 'o'
    invariant count_n: cn + charCount rem 'n' = charCount text 'n'
    decreasing remaining: rem.length
    done_with done: rem = []
  do
    match rem with
    | [] => pure ()
    | c :: cs =>
      if is_b: c = 'b' then
        cb := cb + 1
      else if is_a: c = 'a' then
        ca := ca + 1
      else if is_l: c = 'l' then
        cl := cl + 1
      else if is_o: c = 'o' then
        co := co + 1
      else if is_n: c = 'n' then
        cn := cn + 1
      rem := cs
  let l2 := cl / 2
  let o2 := co / 2
  return Nat.min cb (Nat.min ca (Nat.min l2 (Nat.min o2 cn)))

end Implementation

section Proof

@[simp]
theorem charCount_nil (c : Char) : charCount [] c = 0 := rfl

@[simp]
theorem charCount_cons_self (c : Char) (cs : List Char) :
    charCount (c :: cs) c = charCount cs c + 1 := by
  unfold charCount
  simp

@[simp]
theorem charCount_cons_b_a (cs : List Char) : charCount ('b' :: cs) 'a' = charCount cs 'a' := rfl
@[simp]
theorem charCount_cons_b_l (cs : List Char) : charCount ('b' :: cs) 'l' = charCount cs 'l' := rfl
@[simp]
theorem charCount_cons_b_o (cs : List Char) : charCount ('b' :: cs) 'o' = charCount cs 'o' := rfl
@[simp]
theorem charCount_cons_b_n (cs : List Char) : charCount ('b' :: cs) 'n' = charCount cs 'n' := rfl

@[simp]
theorem charCount_cons_a_b (cs : List Char) : charCount ('a' :: cs) 'b' = charCount cs 'b' := rfl
@[simp]
theorem charCount_cons_a_l (cs : List Char) : charCount ('a' :: cs) 'l' = charCount cs 'l' := rfl
@[simp]
theorem charCount_cons_a_o (cs : List Char) : charCount ('a' :: cs) 'o' = charCount cs 'o' := rfl
@[simp]
theorem charCount_cons_a_n (cs : List Char) : charCount ('a' :: cs) 'n' = charCount cs 'n' := rfl

@[simp]
theorem charCount_cons_l_b (cs : List Char) : charCount ('l' :: cs) 'b' = charCount cs 'b' := rfl
@[simp]
theorem charCount_cons_l_a (cs : List Char) : charCount ('l' :: cs) 'a' = charCount cs 'a' := rfl
@[simp]
theorem charCount_cons_l_o (cs : List Char) : charCount ('l' :: cs) 'o' = charCount cs 'o' := rfl
@[simp]
theorem charCount_cons_l_n (cs : List Char) : charCount ('l' :: cs) 'n' = charCount cs 'n' := rfl

@[simp]
theorem charCount_cons_o_b (cs : List Char) : charCount ('o' :: cs) 'b' = charCount cs 'b' := rfl
@[simp]
theorem charCount_cons_o_a (cs : List Char) : charCount ('o' :: cs) 'a' = charCount cs 'a' := rfl
@[simp]
theorem charCount_cons_o_l (cs : List Char) : charCount ('o' :: cs) 'l' = charCount cs 'l' := rfl
@[simp]
theorem charCount_cons_o_n (cs : List Char) : charCount ('o' :: cs) 'n' = charCount cs 'n' := rfl

@[simp]
theorem charCount_cons_n_b (cs : List Char) : charCount ('n' :: cs) 'b' = charCount cs 'b' := rfl
@[simp]
theorem charCount_cons_n_a (cs : List Char) : charCount ('n' :: cs) 'a' = charCount cs 'a' := rfl
@[simp]
theorem charCount_cons_n_l (cs : List Char) : charCount ('n' :: cs) 'l' = charCount cs 'l' := rfl
@[simp]
theorem charCount_cons_n_o (cs : List Char) : charCount ('n' :: cs) 'o' = charCount cs 'o' := rfl

theorem postcondition_from_counts (text : List Char) (cb ca cl co cn : Nat)
    (hb : cb = charCount text 'b')
    (ha : ca = charCount text 'a')
    (hl : cl = charCount text 'l')
    (ho : co = charCount text 'o')
    (hn : cn = charCount text 'n') :
    postcondition text (Nat.min cb (Nat.min ca (Nat.min (cl / 2) (Nat.min (co / 2) cn)))) := by
  subst cb
  subst ca
  subst cl
  subst co
  subst cn
  unfold postcondition feasibleBalloons
  set b := charCount text 'b'
  set a := charCount text 'a'
  set l := charCount text 'l'
  set o := charCount text 'o'
  set n := charCount text 'n'
  set ans := Nat.min b (Nat.min a (Nat.min (l / 2) (Nat.min (o / 2) n)))
  constructor
  · -- Feasibility
    have hb_le : ans ≤ b := Nat.min_le_left b _
    have ha_le : ans ≤ a := Nat.le_trans (Nat.min_le_right b _) (Nat.min_le_left a _)
    have hl2_le : ans ≤ l / 2 :=
      Nat.le_trans (Nat.min_le_right b _)
        (Nat.le_trans (Nat.min_le_right a _) (Nat.min_le_left (l / 2) _))
    have ho2_le : ans ≤ o / 2 :=
      Nat.le_trans (Nat.min_le_right b _)
        (Nat.le_trans (Nat.min_le_right a _)
          (Nat.le_trans (Nat.min_le_right (l / 2) _) (Nat.min_le_left (o / 2) _)))
    have hn_le : ans ≤ n :=
      Nat.le_trans (Nat.min_le_right b _)
        (Nat.le_trans (Nat.min_le_right a _)
          (Nat.le_trans (Nat.min_le_right (l / 2) _) (Nat.min_le_right (o / 2) n)))
    have hl_mul : 2 * ans ≤ l := by
      have h : ans * 2 ≤ l := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).1 hl2_le
      rwa [Nat.mul_comm] at h
    have ho_mul : 2 * ans ≤ o := by
      have h : ans * 2 ≤ o := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).1 ho2_le
      rwa [Nat.mul_comm] at h
    exact ⟨hb_le, ha_le, hl_mul, ho_mul, hn_le⟩
  · -- Maximality
    intro k hk
    rcases hk with ⟨hkb, hka, hkl, hko, hkn⟩
    have hkl2 : k ≤ l / 2 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
      rwa [Nat.mul_comm]
    have hko2 : k ≤ o / 2 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
      rwa [Nat.mul_comm]
    exact Nat.le_min.mpr ⟨hkb, Nat.le_min.mpr ⟨hka, Nat.le_min.mpr ⟨hkl2, Nat.le_min.mpr ⟨hko2, hkn⟩⟩⟩⟩

prove_correct maxNumberOfBalloons by
  velvet_vcgen [maxNumberOfBalloons, postcondition, charCount] with try finish
  case max_balloons =>
    rename_i text
    have hb : cb = charCount text 'b' := by simp_all [charCount]
    have ha : ca = charCount text 'a' := by simp_all [charCount]
    have hl : cl = charCount text 'l' := by simp_all [charCount]
    have ho : co = charCount text 'o' := by simp_all [charCount]
    have hn : cn = charCount text 'n' := by simp_all [charCount]
    exact postcondition_from_counts text cb ca cl co cn hb ha hl ho hn
  all_goals subst_vars
  all_goals simp_all [charCount]
  all_goals omega

end Proof

end MaximumNumberOfBalloons
