module

public import Velvet
public meta import Velvet
public import Mathlib.Tactic

set_option maxHeartbeats 10000000

/-!
## Program description

Determine whether `typed` could result from typing `name` where each key press
may repeat a character one or more times.

1. Inputs are two sequences of characters: `name` and `typed`.
2. Typing `name` produces characters in the same order as `name`.
3. Each character `name[k]` is produced at least once in `typed` (normal press)
   and may be repeated additional times contiguously (long press).
4. The overall `typed` output must be exactly the concatenation of these
   contiguous blocks, one block per character position in `name`.
5. Therefore, `typed` can be partitioned into exactly `name.size` nonempty
   consecutive segments; the k-th segment contains only copies of `name[k]`.
6. If such a partition exists, return true; otherwise return false.

The program is expected to run in O(m + n) time and O(1) space.
-/

namespace LongPressedName

section Specs

public def segmentAllEq (typed : Array Char) (start : Nat) (stop : Nat) (c : Char) : Prop :=
  start ≤ stop ∧ stop ≤ typed.size ∧
    ∀ (i : Nat), start ≤ i ∧ i < stop → typed[i]! = c

public def validBreaks (name : Array Char) (typed : Array Char) (breaks : Array Nat) : Prop :=
  breaks.size = name.size + 1 ∧
  breaks[0]! = 0 ∧
  breaks[name.size]! = typed.size ∧
  (∀ (k : Nat), k < name.size → breaks[k]! < breaks[k+1]!) ∧
  (∀ (k : Nat), k < name.size → segmentAllEq typed breaks[k]! breaks[k+1]! name[k]!)

public def isLongPressed (name : Array Char) (typed : Array Char) : Prop :=
  ∃ (breaks : Array Nat), validBreaks name typed breaks

public def precondition (_name : Array Char) (_typed : Array Char) : Prop :=
  True

public def postcondition (name : Array Char) (typed : Array Char) (result : Bool) : Prop :=
  (result = true ↔ isLongPressed name typed)

end Specs

section Implementation

public def checkRec (name : Array Char) (typed : Array Char) (ni : Nat) (ti : Nat) : Bool :=
  if _hti : ti < typed.size then
    let t := typed[ti]!
    if _hni : ni < name.size then
      if t = name[ni]! then
        checkRec name typed (ni + 1) (ti + 1)
      else if 0 < ni ∧ t = name[ni - 1]! then
        checkRec name typed ni (ti + 1)
      else
        false
    else
      if t = name[name.size - 1]! then
        checkRec name typed ni (ti + 1)
      else
        false
  else
    ni == name.size
termination_by typed.size - ti

method isLongPressedName (name : Array Char) (typed : Array Char)
  returns (result : Bool)
  requires valid: precondition name typed
  ensures checked: postcondition name typed result
do
  if name.size == 0 then
    return typed.size == 0
  let mut ni : Nat := 0
  let mut ti : Nat := 0
  let mut ok : Bool := true
  while scanning: ti < typed.size ∧ ok
    invariant continuation:
      (if ok then checkRec name typed ni ti else false) = checkRec name typed 0 0
    decreasing rem_typed: typed.size - ti
    done_with done: ¬(ti < typed.size ∧ ok)
  do
    let t := typed[ti]!
    if ni < name.size then
      if t == name[ni]! then
        ni := ni + 1
      else if 0 < ni && t == name[ni - 1]! then
        pure ()
      else
        ok := false
    else
      if t == name[name.size - 1]! then
        pure ()
      else
        ok := false
    ti := ti + 1
  return ok && (ni == name.size)

end Implementation

section Proof

lemma isLongPressed_nil (typed : Array Char) :
    isLongPressed #[] typed ↔ typed.size = 0 := by
  constructor
  · rintro ⟨breaks, hbreaks⟩
    unfold validBreaks at hbreaks
    have hbsize : breaks.size = 1 := by simp [hbreaks.1]
    have hb0 : breaks[0]! = 0 := hbreaks.2.1
    have hb_last : breaks[0]! = typed.size := by simpa [hbsize] using hbreaks.2.2.1
    rw [← hb_last, hb0]
  · intro h
    refine ⟨#[0], ?_⟩
    unfold validBreaks
    refine ⟨by simp, by simp, by simp [h], by intro k hk; simp at hk, by intro k hk; simp at hk⟩

lemma checkRec_sound (name typed : Array Char) (_h0 : name.size ≠ 0) :
    checkRec name typed 0 0 = true → isLongPressed name typed := by
  intro h
  have h_partition : ∃ breaks : Array Nat, validBreaks name typed breaks := by
    have h_rec : ∀ ni ti, ni ≤ name.size → ti ≤ typed.size → checkRec name typed ni ti = true →
        ∃ breaks : Array Nat, breaks.size = name.size - ni + 1 ∧
        breaks[name.size - ni]! = typed.size ∧
        (∀ k, k < name.size - ni → breaks[k]! < breaks[k + 1]!) ∧
        (∀ k, k < name.size - ni → segmentAllEq typed breaks[k]! breaks[k + 1]! name[ni + k]!) ∧
        (ni = 0 → breaks[0]! = ti) ∧
        (ni > 0 → breaks[0]! ≥ ti ∧ ∀ j, ti ≤ j ∧ j < breaks[0]! → typed[j]! = name[ni - 1]!) := by
      intros ni ti hni hti h_check
      induction' _hn : typed.size - ti using Nat.strong_induction_on with m ih generalizing ni ti
      unfold checkRec at h_check
      split_ifs at h_check; simp_all +decide
      · split_ifs at h_check
        · obtain ⟨breaks, hbreaks⟩ := ih (typed.size - (ti + 1)) (by omega) (ni + 1) (ti + 1) (by omega) (by omega) h_check rfl
          use #[ti] ++ breaks
          refine' ⟨_, _, _, _, _⟩
          · grind
          · rw [show name.size - ni = name.size - (ni + 1) + 1 by omega]
            cases breaks; aesop
          · intro k hk; rcases k with (_ | k) <;> simp_all +decide
            · grind
            · convert hbreaks.2.2.1 k (by omega) using 1 <;> (cases breaks; aesop)
          · intro k hk; rcases k with (_ | k) <;> simp_all +decide
            · refine' ⟨_, _, _⟩
              · grind
              · have h_le : ∀ k < breaks.size, breaks[k]! ≤ breaks[breaks.size - 1]! := by
                  intro k hk
                  have h_le' : ∀ k l, k ≤ l → l < breaks.size → breaks[k]! ≤ breaks[l]! := by
                    intros k l hkl hl
                    induction' hkl with k' _hk' ih'
                    · norm_num
                    · exact le_trans (ih' (Nat.lt_of_succ_lt hl)) (le_of_lt (hbreaks.2.2.1 k' (by omega)))
                  exact h_le' _ _ (Nat.le_sub_one_of_lt hk) (Nat.sub_lt (by linarith) zero_lt_one)
                grind
              · intro i hi; cases lt_or_eq_of_le hi.1 <;> aesop
            · convert hbreaks.2.2.2.1 k (by omega) using 1
              · cases breaks; aesop
              · cases breaks; aesop
              · ac_rfl
          · cases breaks; aesop
        · obtain ⟨breaks, hbreaks⟩ := ih (typed.size - (ti + 1)) (by omega) ni (ti + 1) hni (by linarith) h_check.right (by rfl)
          grind
      · grind
      · use #[typed.size]
        grind
    specialize h_rec 0 0 (Nat.zero_le _) (Nat.zero_le _) h
    unfold validBreaks; aesop
  exact h_partition

public def hasSolutionFrom (name typed : Array Char) (ni ti : Nat) : Prop :=
  ∃ (breaks : Array Nat),
    breaks.size = name.size - ni + 1 ∧
    breaks[name.size - ni]! = typed.size ∧
    (∀ k, k < name.size - ni → breaks[k]! < breaks[k + 1]!) ∧
    (∀ k, k < name.size - ni → segmentAllEq typed (breaks[k]!) (breaks[k + 1]!) (name[ni + k]!)) ∧
    (ni = 0 → breaks[0]! = ti) ∧
    (ni > 0 → breaks[0]! ≥ ti ∧ (∀ j, ti ≤ j → j < breaks[0]! → typed[j]! = name[ni - 1]!))

lemma isLP_to_hasSol (name typed : Array Char) (_h0 : 0 < name.size) :
    isLongPressed name typed → hasSolutionFrom name typed 0 0 := by
  intro h
  obtain ⟨breaks, h_valid⟩ := h
  use breaks
  cases h_valid; aesop

lemma hasSol_to_checkRec (name typed : Array Char) (ni ti : Nat)
    (hni : ni ≤ name.size) (_hti : ti ≤ typed.size) (_h0 : 0 < name.size)
    (hsol : hasSolutionFrom name typed ni ti) :
    checkRec name typed ni ti = true := by
  induction' _hn : typed.size - ti with n ih generalizing ni ti
  · obtain ⟨breaks, hbreaks⟩ := hsol
    cases hni.eq_or_lt <;> simp_all +decide [Nat.sub_eq_iff_eq_add]
    · unfold checkRec; aesop
    · have h_contra : ∀ k < name.size - ni, breaks[k]! < breaks[k + 1]! := hbreaks.2.2.1
      have h_contra' : ∀ k < name.size - ni + 1, breaks[k]! ≥ breaks[0]! + k := by
        intro k hk
        induction' k with k' ih'
        · norm_num
        · linarith [ih' (Nat.lt_of_succ_lt hk), h_contra k' (Nat.lt_of_succ_lt_succ hk)]
      grind +ring
  · obtain ⟨breaks, h1, _h2, _h3, h4, _h5⟩ := hsol
    unfold checkRec; split_ifs <;> simp_all +decide
    · split_ifs <;> simp_all +decide [segmentAllEq]
      · convert ih (ni + 1) (ti + 1) (by linarith) (by omega) _ _ using 1
        · use breaks.drop 1
          simp_all +decide [add_comm]
          refine' ⟨_, _, _, _, _⟩
          all_goals generalize_proofs at *
          · omega
          · grind +ring
          · grind +ring
          · intro k hk; specialize h4 (k + 1) (by omega); simp_all +decide [add_comm, add_left_comm]
            refine' ⟨_, _, _⟩
            all_goals generalize_proofs at *
            · grind
            · grind +ring
            · grind +ring
          · rcases ni <;> simp_all +decide <;> (grind +ring)
        · omega
      · have : typed[ti]! = name[ni - 1]! := by
          specialize h4 0; simp_all +decide
          grind +ring
        generalize_proofs at *
        by_cases hni_pos : 0 < ni <;> simp_all +decide
        convert ih ni (ti + 1) hni (by linarith) _ _ using 1
        generalize_proofs at *
        use breaks
        generalize_proofs at *
        refine' ⟨h1, _, _, _, _, _⟩ <;> simp_all +decide [segmentAllEq]
        · exact fun k hk i hi₁ hi₂ => h4 k hk |>.2.2 i hi₁ hi₂ ▸ rfl
        · linarith
        · specialize h4 0; simp_all +decide
          grind
        · omega
    · cases lt_or_eq_of_le hni <;> simp_all +decide [Nat.sub_eq_zero_of_le]
      apply ih name.size (ti + 1) (by linarith) (by linarith) (by use #[typed.size]; grind) (by omega)

lemma checkRec_complete (name typed : Array Char) (h0 : name.size ≠ 0) :
    isLongPressed name typed → checkRec name typed 0 0 = true := by
  intro hlp
  exact hasSol_to_checkRec name typed 0 0 (Nat.zero_le _) (Nat.zero_le _) (by omega)
    (isLP_to_hasSol name typed (by omega) hlp)

theorem isLongPressedPure_correct (name typed : Array Char) (h0 : name.size ≠ 0) :
    (checkRec name typed 0 0 = true ↔ isLongPressed name typed) :=
  ⟨checkRec_sound name typed h0, checkRec_complete name typed h0⟩

prove_correct isLongPressedName by
  velvet_vcgen [isLongPressedName, postcondition] with try finish
  case checked =>
    rename_i name typed
    unfold postcondition
    have h0 : name.size = 0 := by simpa using if_cond
    have hnil : name = #[] := Array.eq_empty_of_size_eq_zero h0
    rw [hnil]
    have hnil_lp := isLongPressed_nil typed
    simp only [beq_iff_eq]
    exact hnil_lp.symm
  case checked =>
    rename_i name typed
    unfold postcondition
    have h0 : name.size ≠ 0 := by
      intro h; revert if_cond; simp [h]
    rw [← isLongPressedPure_correct name typed h0]
    by_cases hok : ok = true
    · simp only [hok, ↓reduceIte] at continuation
      have hti : ¬ti < typed.size := by
        intro hti; exact done ⟨hti, hok⟩
      rw [checkRec.eq_def] at continuation
      simp only [hti, ↓reduceDIte] at continuation
      simp only [hok, Bool.true_and, continuation]
    · have hok' : ok = false := by cases ok <;> [rfl; contradiction]
      simp only [hok', Bool.false_eq_true, ↓reduceIte] at continuation
      simp only [hok', Bool.false_and, continuation.symm]
  case continuation =>
    rename_i name typed
    have hok : ok = true := scanning.2
    have hti : ti < typed.size := scanning.1
    have heq : (typed[ti]! = name[ni]!) ↔ True := by
      simp [show typed[ti]! = name[ni]! by simpa using if_cond_2]
    simp only [hok, ↓reduceIte] at continuation ⊢
    rw [← continuation]
    conv_rhs => rw [checkRec.eq_def]
    simp only [hti, ↓reduceDIte, if_cond_1, heq, ↓reduceIte]
  case continuation =>
    rename_i name typed
    have hok : ok = true := scanning.2
    have hti : ti < typed.size := scanning.1
    have hne : (typed[ti]! = name[ni]!) ↔ False := by
      simp [show typed[ti]! ≠ name[ni]! from fun h => by simp [h] at if_cond_2]
    have hlong : (0 < ni ∧ typed[ti]! = name[ni - 1]!) ↔ True := by
      have : 0 < ni ∧ typed[ti]! = name[ni - 1]! := by simpa using if_cond_3
      simp [this]
    simp only [hok, ↓reduceIte] at continuation ⊢
    rw [← continuation]
    conv_rhs => rw [checkRec.eq_def]
    simp only [hti, ↓reduceDIte, if_cond_1, hne, hlong, ↓reduceIte]
  case continuation =>
    rename_i name typed
    have hok : ok = true := scanning.2
    have hti : ti < typed.size := scanning.1
    have hne : (typed[ti]! = name[ni]!) ↔ False := by
      simp [show typed[ti]! ≠ name[ni]! from fun h => by simp [h] at if_cond_2]
    have hnot_long : (0 < ni ∧ typed[ti]! = name[ni - 1]!) ↔ False := by
      simp [show ¬(0 < ni ∧ typed[ti]! = name[ni - 1]!) from fun h => by simp [h.1, h.2] at if_cond_3]
    simp only [hok, ↓reduceIte] at continuation
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← continuation]
    conv_rhs => rw [checkRec.eq_def]
    simp only [hti, ↓reduceDIte, if_cond_1, hne, hnot_long, ↓reduceIte]
  case continuation =>
    rename_i name typed
    have hok : ok = true := scanning.2
    have hti : ti < typed.size := scanning.1
    have heq : (typed[ti]! = name[name.size - 1]!) ↔ True := by
      simp [show typed[ti]! = name[name.size - 1]! by simpa using if_cond_2]
    simp only [hok, ↓reduceIte] at continuation ⊢
    rw [← continuation]
    conv_rhs => rw [checkRec.eq_def]
    simp only [hti, ↓reduceDIte, if_cond_1, heq, ↓reduceIte]
  case continuation =>
    rename_i name typed
    have hok : ok = true := scanning.2
    have hti : ti < typed.size := scanning.1
    have hne : (typed[ti]! = name[name.size - 1]!) ↔ False := by
      simp [show typed[ti]! ≠ name[name.size - 1]! from fun h => by simp [h] at if_cond_2]
    simp only [hok, ↓reduceIte] at continuation
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← continuation]
    conv_rhs => rw [checkRec.eq_def]
    simp only [hti, ↓reduceDIte, if_cond_1, hne, ↓reduceIte]

end Proof

end LongPressedName
