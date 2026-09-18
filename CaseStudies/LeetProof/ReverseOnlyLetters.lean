module

public import Velvet
public meta import Velvet

/-!
## Program description

Reverse only the English letters in a character sequence, keeping non-letters
fixed.

1. Input is a finite sequence of characters.
2. A character is considered an English letter exactly when it is an ASCII
   uppercase letter ('A'..'Z') or an ASCII lowercase letter ('a'..'z').
3. Every non-letter character must stay at the same index in the output.
4. The set of indices that contain letters must be the same in input and output.
5. Reading only the letters from left to right in the output yields the reverse
   of the letters read from left to right in the input.
6. The output has the same length as the input.

The program is expected to run in O(n) time and O(n) space.
-/

namespace ReverseOnlyLetters

section Specs

public def isAsciiUpper (c : Char) : Bool :=
  ('A'.toNat ≤ c.toNat) && (c.toNat ≤ 'Z'.toNat)

public def isAsciiLower (c : Char) : Bool :=
  ('a'.toNat ≤ c.toNat) && (c.toNat ≤ 'z'.toNat)

public def isLetter (c : Char) : Bool :=
  isAsciiUpper c || isAsciiLower c

public def letters (s : List Char) : List Char :=
  s.filter (fun c => isLetter c)

public def precondition (_s : List Char) : Prop :=
  True

public def postcondition (s : List Char) (result : List Char) : Prop :=
  result.length = s.length ∧
  (∀ (i : Nat), i < s.length → (isLetter s[i]! = false) → result[i]! = s[i]!) ∧
  (∀ (i : Nat), i < s.length → isLetter result[i]! = isLetter s[i]!) ∧
  letters result = (letters s).reverse

end Specs

section Implementation

public def extractLettersGo (rem : List Char) (acc : List Char) : List Char :=
  match rem with
  | [] => acc
  | x :: xs =>
      if isLetter x then extractLettersGo xs (x :: acc)
      else extractLettersGo xs acc

public def fillGo (rem : List Char) (ls : List Char) (acc : List Char) : List Char :=
  match rem with
  | [] => acc.reverse
  | x :: xs =>
      if isLetter x then
        match ls with
        | [] => fillGo xs [] (x :: acc)
        | l :: ls' => fillGo xs ls' (l :: acc)
      else
        fillGo xs ls (x :: acc)

public def reverseOnlyLettersPure (s : List Char) : List Char :=
  fillGo s (extractLettersGo s []) []

method reverseOnlyLetters (s : List Char)
  returns (result : List Char)
  requires valid: precondition s
  ensures reversed: postcondition s result
do
  let mut rem : List Char := s
  let mut revLetters : List Char := []
  while' collecting: rem ≠ []
    invariant collect_continuation:
      extractLettersGo rem revLetters = extractLettersGo s []
    decreasing rem_len: rem.length
    done_with collected: rem = []
  do
    match rem with
    | [] => pure ()
    | c :: cs =>
      if isLetter c then
        revLetters := c :: revLetters
      rem := cs
  let mut scan : List Char := s
  let mut ls : List Char := revLetters
  let mut acc : List Char := []
  while' rebuilding: scan ≠ []
    invariant rebuild_continuation:
      fillGo scan ls acc = reverseOnlyLettersPure s
    decreasing scan_len: scan.length
    done_with rebuilt: scan = []
  do
    match scan with
    | [] => pure ()
    | c :: cs =>
      if isLetter c then
        match ls with
        | [] =>
          acc := c :: acc
        | l :: ls' =>
          acc := l :: acc
          ls := ls'
      else
        acc := c :: acc
      scan := cs
  return acc.reverse

end Implementation

section Proof

theorem extractLettersGo_eq : ∀ xs acc, extractLettersGo xs acc = (letters xs).reverse ++ acc := by
  intro xs
  induction xs with
  | nil =>
      intro acc
      simp [extractLettersGo, letters]
  | cons x xs ih =>
      intro acc
      rw [extractLettersGo.eq_def]
      cases hx : isLetter x
      · simp only [hx, Bool.false_eq_true, ↓reduceIte]
        rw [ih acc]
        unfold letters
        simp [List.filter, hx]
      · simp only [hx, ↓reduceIte]
        rw [ih (x :: acc)]
        unfold letters
        simp [List.filter, hx, List.reverse_cons, List.append_assoc]

theorem extractLettersGo_nil (s : List Char) : extractLettersGo s [] = (letters s).reverse := by
  simpa using extractLettersGo_eq s []

public def fill (xs : List Char) (ls : List Char) : List Char :=
  match xs with
  | [] => []
  | x :: xs' =>
      if isLetter x then
        match ls with
        | [] => x :: fill xs' []
        | l :: ls' => l :: fill xs' ls'
      else
        x :: fill xs' ls

theorem fillGo_eq : ∀ xs ls acc, fillGo xs ls acc = acc.reverse ++ fill xs ls := by
  intro xs
  induction xs with
  | nil =>
      intro ls acc
      simp [fillGo, fill]
  | cons x xs ih =>
      intro ls acc
      rw [fillGo.eq_def]
      cases hx : isLetter x
      · simp only [hx, Bool.false_eq_true, ↓reduceIte]
        rw [ih ls (x :: acc)]
        simp [fill, hx, List.append_assoc]
      · simp only [hx, ↓reduceIte]
        cases ls with
        | nil =>
            simp only []
            rw [ih [] (x :: acc)]
            simp [fill, hx, List.append_assoc]
        | cons l ls' =>
            simp only []
            rw [ih ls' (l :: acc)]
            simp [fill, hx, List.append_assoc]

theorem reverseOnlyLettersPure_eq (s : List Char) :
    reverseOnlyLettersPure s = fill s (letters s).reverse := by
  unfold reverseOnlyLettersPure
  rw [extractLettersGo_nil]
  simp [fillGo_eq]

theorem fill_length : ∀ xs ls, (fill xs ls).length = xs.length := by
  intro xs
  induction xs with
  | nil => intro ls; simp [fill]
  | cons x xs ih =>
      intro ls
      rw [fill.eq_def]
      cases hx : isLetter x
      · simp only [hx, Bool.false_eq_true, ↓reduceIte, List.length_cons]
        rw [ih ls]
      · simp only [hx, ↓reduceIte]
        cases ls with
        | nil => simp [ih]
        | cons l ls' => simp [ih]

theorem fill_get_nonletter :
    ∀ xs ls (i : Nat), i < xs.length → isLetter xs[i]! = false → (fill xs ls)[i]! = xs[i]! := by
  intro xs
  induction xs with
  | nil =>
      intro ls i hi
      simp at hi
  | cons x xs ih =>
      intro ls i hi hnot
      rw [fill.eq_def]
      cases i with
      | zero =>
          have hxnot : isLetter x = false := by simpa [List.getElem!_cons_zero] using hnot
          simp only [hxnot, Bool.false_eq_true, ↓reduceIte, List.getElem!_cons_zero]
      | succ i =>
          have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
          have hnot' : isLetter xs[i]! = false := by simpa [List.getElem!_cons_succ] using hnot
          cases hx : isLetter x
          · simp only [hx, Bool.false_eq_true, ↓reduceIte, List.getElem!_cons_succ]
            exact ih ls i hi' hnot'
          · simp only [hx, ↓reduceIte]
            cases ls with
            | nil =>
                simp only [List.getElem!_cons_succ]
                exact ih [] i hi' hnot'
            | cons l ls' =>
                simp only [List.getElem!_cons_succ]
                exact ih ls' i hi' hnot'

theorem all_letters_mem_rev (s : List Char) :
    ∀ c ∈ (letters s).reverse, isLetter c = true := by
  intro c hc
  have : c ∈ letters s := by simpa using (List.mem_reverse.mp hc)
  unfold letters at this
  exact (List.mem_filter.mp this).2

theorem fill_mask :
    ∀ xs ls, (∀ c ∈ ls, isLetter c = true) →
    ∀ (i : Nat), i < xs.length → isLetter (fill xs ls)[i]! = isLetter xs[i]! := by
  intro xs
  induction xs with
  | nil =>
      intro ls _hall i hi
      simp at hi
  | cons x xs ih =>
      intro ls hall i hi
      rw [fill.eq_def]
      cases i with
      | zero =>
          cases hx : isLetter x
          · simp only [hx, Bool.false_eq_true, ↓reduceIte, List.getElem!_cons_zero]
          · simp only [hx, ↓reduceIte]
            cases ls with
            | nil => simp [hx]
            | cons l ls' =>
                have hl : isLetter l = true := hall l (by simp)
                simp [hl, hx]
      | succ i =>
          have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
          cases hx : isLetter x
          · simp only [hx, Bool.false_eq_true, ↓reduceIte, List.getElem!_cons_succ]
            exact ih ls hall i hi'
          · simp only [hx, ↓reduceIte]
            cases ls with
            | nil =>
                exact ih [] (by intro c hc; cases hc) i hi'
            | cons l ls' =>
                have hall' : ∀ c ∈ ls', isLetter c = true := by
                  intro c hc; exact hall c (by simp [hc])
                exact ih ls' hall' i hi'

theorem fill_letters_eq :
    ∀ xs ls, (∀ c ∈ ls, isLetter c = true) →
    ls.length = (letters xs).length →
    letters (fill xs ls) = ls := by
  intro xs
  induction xs with
  | nil =>
      intro ls _hall hlen
      have : ls = [] := by
        apply List.eq_nil_of_length_eq_zero
        unfold letters at hlen
        simpa using hlen
      subst this
      simp [fill, letters]
  | cons x xs ih =>
      intro ls hall hlen
      rw [fill.eq_def]
      cases hx : isLetter x
      · simp only [hx, Bool.false_eq_true, ↓reduceIte]
        have hlen' : ls.length = (letters xs).length := by
          unfold letters at hlen ⊢
          simp only [List.filter, hx] at hlen
          exact hlen
        unfold letters at ⊢
        simp only [List.filter, hx]
        exact ih ls hall hlen'
      · simp only [hx, ↓reduceIte]
        cases ls with
        | nil =>
            exfalso
            have hpos : 0 < (letters (x :: xs)).length := by
              unfold letters; simp [List.filter, hx]
            have : (letters (x :: xs)).length = 0 := by simpa using hlen.symm
            omega
        | cons l ls' =>
            have hl : isLetter l = true := hall l (by simp)
            have hall' : ∀ c ∈ ls', isLetter c = true := by
              intro c hc; exact hall c (by simp [hc])
            have hlen' : ls'.length = (letters xs).length := by
              unfold letters at hlen ⊢
              simp only [List.filter, hx, List.length_cons] at hlen
              exact Nat.succ.inj hlen
            unfold letters at ⊢
            simp only [List.filter, hl, List.cons.injEq, true_and]
            exact ih ls' hall' hlen'

theorem reverseOnlyLettersPure_correct (s : List Char) :
    postcondition s (reverseOnlyLettersPure s) := by
  rw [reverseOnlyLettersPure_eq]
  unfold postcondition
  refine ⟨fill_length s _, ?_, ?_, ?_⟩
  · intro i hi hnot
    exact fill_get_nonletter s _ i hi hnot
  · intro i hi
    exact fill_mask s _ (all_letters_mem_rev s) i hi
  · have hall := all_letters_mem_rev s
    have hlen : ((letters s).reverse).length = (letters s).length := by simp
    exact fill_letters_eq s ((letters s).reverse) hall hlen

prove_correct reverseOnlyLetters by
  velvet_vcgen [reverseOnlyLetters, postcondition] with try finish
  case rebuild_continuation =>
    simp [extractLettersGo, collected] at collect_continuation
    rw [collect_continuation, reverseOnlyLettersPure]
  case reversed =>
    simp [fillGo, rebuilt] at rebuild_continuation
    rw [rebuild_continuation]
    exact reverseOnlyLettersPure_correct _
  case rebuild_continuation =>
    rw [h_cons, h_nil] at rebuild_continuation
    rw [fillGo.eq_def] at rebuild_continuation
    simp [if_cond] at rebuild_continuation
    rw [h_nil]
    exact rebuild_continuation
  case rebuild_continuation =>
    rw [h_cons, h_cons_1] at rebuild_continuation
    rw [fillGo.eq_def] at rebuild_continuation
    simp [if_cond] at rebuild_continuation
    exact rebuild_continuation
  case rebuild_continuation =>
    rw [h_cons] at rebuild_continuation
    rw [fillGo.eq_def] at rebuild_continuation
    simp [if_cond] at rebuild_continuation
    exact rebuild_continuation
  case collect_continuation =>
    rw [h_cons] at collect_continuation
    rw [extractLettersGo.eq_def] at collect_continuation
    simp [if_cond] at collect_continuation
    exact collect_continuation
  case collect_continuation =>
    rw [h_cons] at collect_continuation
    rw [extractLettersGo.eq_def] at collect_continuation
    simp [if_cond] at collect_continuation
    exact collect_continuation


end Proof

end ReverseOnlyLetters
