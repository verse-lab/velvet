import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def decode (encoded : List (Char × Nat)) : List Char :=
  encoded.flatMap (fun p => List.replicate p.2 p.1)


def allPositiveCounts (encoded : List (Char × Nat)) : Prop :=
  ∀ p ∈ encoded, p.2 > 0


def noConsecutiveSameChar (encoded : List (Char × Nat)) : Prop :=
  ∀ i : Nat, i + 1 < encoded.length → (encoded[i]!).1 ≠ (encoded[i + 1]!).1



def ensures1 (s : String) (result : List (Char × Nat)) :=
  allPositiveCounts result


def ensures2 (s : String) (result : List (Char × Nat)) :=
  noConsecutiveSameChar result


def ensures3 (s : String) (result : List (Char × Nat)) :=
  decode result = s.toList

def precondition (s : String) :=
  True

def postcondition (s : String) (result : List (Char × Nat)) :=
  ensures1 s result ∧
  ensures2 s result ∧
  ensures3 s result


def test1_s : String := ""

def test1_Expected : List (Char × Nat) := []

def test3_s : String := "abbbcccaa"

def test3_Expected : List (Char × Nat) := [('a', 1), ('b', 3), ('c', 3), ('a', 2)]

def test4_s : String := "xyz"

def test4_Expected : List (Char × Nat) := [('x', 1), ('y', 1), ('z', 1)]







section Proof
theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 allPositiveCounts noConsecutiveSameChar decode
  unfold test1_s test1_Expected
  constructor
  · -- ensures1: ∀ p ∈ [], p.2 > 0
    intro p hp
    exact absurd hp (List.not_mem_nil)
  · constructor
    · -- ensures2: ∀ i, i + 1 < [].length → ...
      intro i hi
      simp [List.length_nil] at hi
    · -- ensures3: decode [] = "".toList
      simp [List.flatMap_nil]

theorem test3_precondition :
  precondition test3_s := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition_0
    (h_unfold : postcondition test3_s test3_Expected ↔ ensures1 test3_s test3_Expected ∧ ensures2 test3_s test3_Expected ∧ ensures3 test3_s test3_Expected)
    : ensures1 test3_s test3_Expected := by
    unfold ensures1 allPositiveCounts test3_Expected
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide

theorem test3_postcondition_1
    (h_ensures1 : ensures1 test3_s test3_Expected)
    (h_unfold : postcondition test3_s test3_Expected ↔ ensures1 test3_s test3_Expected ∧ ensures2 test3_s test3_Expected ∧ ensures3 test3_s test3_Expected)
    : ensures2 test3_s test3_Expected := by
    unfold ensures2 noConsecutiveSameChar test3_Expected
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    -- hi : i + 1 < 4, so i < 3, meaning i ∈ {0, 1, 2}
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | 2 => native_decide
    | n + 3 => omega

theorem test3_postcondition :
  postcondition test3_s test3_Expected := by
  -- First, unfold all definitions to expose the concrete computations
  have h_unfold : postcondition test3_s test3_Expected = 
    (ensures1 test3_s test3_Expected ∧ ensures2 test3_s test3_Expected ∧ ensures3 test3_s test3_Expected) := by
    (try simp at *; expose_names); exact Eq.to_iff rfl; done
  -- Unfold ensures1: allPositiveCounts for the concrete list
  have h_ensures1 : ensures1 test3_s test3_Expected := by
    (try simp at *; expose_names); exact (test3_postcondition_0 h_unfold); done
  -- Unfold ensures2: noConsecutiveSameChar - check consecutive pairs have different first elements
  have h_ensures2 : ensures2 test3_s test3_Expected := by
    (try simp at *; expose_names); exact (test3_postcondition_1 h_ensures1 h_unfold); done
  -- Unfold ensures3: decode result equals original string
  -- decode [('a', 1), ('b', 3), ('c', 3), ('a', 2)] 
  -- = ['a'] ++ ['b', 'b', 'b'] ++ ['c', 'c', 'c'] ++ ['a', 'a']
  -- = ['a', 'b', 'b', 'b', 'c', 'c', 'c', 'a', 'a']
  -- = "abbbcccaa".toList
  have h_ensures3 : ensures3 test3_s test3_Expected := by
    (try simp at *; expose_names); exact rfl; done
  -- Combine all three ensures into the postcondition
  exact ⟨h_ensures1, h_ensures2, h_ensures3⟩

theorem test4_precondition :
  precondition test4_s := by
  intros; expose_names; exact (trivial); done

theorem test4_postcondition :
  postcondition test4_s test4_Expected := by
  unfold postcondition ensures1 ensures2 ensures3
  unfold test4_s test4_Expected
  refine ⟨?_, ?_, ?_⟩
  · -- ensures1: allPositiveCounts
    unfold allPositiveCounts
    intro p hp
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · -- ensures2: noConsecutiveSameChar
    unfold noConsecutiveSameChar
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    match i with
    | 0 => native_decide
    | 1 => native_decide
    | n + 2 => omega
  · -- ensures3: decode result = s.toList
    unfold decode
    native_decide

theorem uniqueness_0
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    : allPositiveCounts ret1 := by
    exact hpost1.1

theorem uniqueness_1
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    : noConsecutiveSameChar ret1 := by
    exact hpost1.2.1

theorem uniqueness_2
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    : decode ret1 = s.data := by
    have h3 : ensures3 s ret1 := hpost1.2.2
    unfold ensures3 at h3
    simp only [String.toList] at h3
    exact h3

theorem uniqueness_3
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    : allPositiveCounts ret2 := by
    intros; expose_names; exact (uniqueness_0 s _hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_4
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    : noConsecutiveSameChar ret2 := by
    intros; expose_names; exact (uniqueness_1 s _hpre ret2 ret1 hpost2 hpost1 h2_pos); done

theorem uniqueness_5
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    : decode ret2 = s.data := by
    intros; expose_names; exact (uniqueness_2 s _hpre ret2 ret1 hpost2 hpost1 h2_pos h2_nocons); done

theorem uniqueness_6
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    : decode ret1 = decode ret2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_7_0
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    (h_same_decode : decode ret1 = decode ret2)
    : ∀ (enc : List (Char × ℕ)), allPositiveCounts enc → decode enc = [] → enc = [] := by
    intro enc h_pos h_decode_nil
    match enc with
    | [] => rfl
    | p :: rest =>
      -- p is in enc, so p.2 > 0
      have hp_mem : p ∈ (p :: rest) := by simp
      have hp_pos : p.2 > 0 := h_pos p hp_mem
      -- decode of p :: rest = replicate p.2 p.1 ++ decode rest
      unfold decode at h_decode_nil
      simp only [List.flatMap_cons] at h_decode_nil
      -- If the concatenation is empty, both parts must be empty
      have h_both_nil := List.append_eq_nil_iff.mp h_decode_nil
      have h_repl_nil : List.replicate p.2 p.1 = [] := h_both_nil.1
      -- But replicate n a = [] implies n = 0
      have h_len : (List.replicate p.2 p.1).length = 0 := by rw [h_repl_nil]; rfl
      simp only [List.length_replicate] at h_len
      -- This contradicts p.2 > 0
      omega

theorem uniqueness_7_1
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    (h_same_decode : decode ret1 = decode ret2)
    (h_decode_nil : ∀ (enc : List (Char × ℕ)), allPositiveCounts enc → decode enc = [] → enc = [])
    : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → ¬decode ((c, n) :: rest) = [] := by
    intro c n rest hn h
    unfold decode at h
    simp only [List.flatMap_cons] at h
    rw [List.append_eq_nil_iff] at h
    obtain ⟨h_repl, _⟩ := h
    have h_len : (List.replicate n c).length = n := List.length_replicate
    rw [h_repl] at h_len
    simp at h_len
    omega

theorem uniqueness_7_2
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    (h_same_decode : decode ret1 = decode ret2)
    (h_decode_nil : ∀ (enc : List (Char × ℕ)), allPositiveCounts enc → decode enc = [] → enc = [])
    (h_decode_cons_nonempty : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → ¬decode ((c, n) :: rest) = [])
    : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → (decode ((c, n) :: rest)).head? = some c := by
    intro c n rest hn
    unfold decode
    simp only [List.flatMap_cons]
    rw [List.head?_append]
    rw [List.head?_replicate]
    have h_n_ne_zero : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    simp only [h_n_ne_zero, ↓reduceIte, Option.some_or]

theorem uniqueness_7_3
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    (h_same_decode : decode ret1 = decode ret2)
    (h_decode_nil : ∀ (enc : List (Char × ℕ)), allPositiveCounts enc → decode enc = [] → enc = [])
    (h_decode_cons_nonempty : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → ¬decode ((c, n) :: rest) = [])
    (h_decode_head : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → (decode ((c, n) :: rest)).head? = some c)
    : ∀ (c1 c2 : Char) (n1 n2 : ℕ) (rest1 rest2 : List Char), 0 < n1 → 0 < n2 → List.replicate n1 c1 ++ rest1 = List.replicate n2 c2 ++ rest2 → c1 = c2 := by
    intro c1 c2 n1 n2 rest1 rest2 hn1 hn2 heq
    -- Since n1 > 0, we have n1 = (n1 - 1) + 1
    have h1 : n1 = (n1 - 1) + 1 := by omega
    -- Since n2 > 0, we have n2 = (n2 - 1) + 1
    have h2 : n2 = (n2 - 1) + 1 := by omega
    -- Rewrite using replicate_succ
    rw [h1, List.replicate_succ] at heq
    rw [h2, List.replicate_succ] at heq
    -- Now heq : c1 :: (List.replicate (n1 - 1) c1 ++ rest1) = c2 :: (List.replicate (n2 - 1) c2 ++ rest2)
    simp only [List.cons_append] at heq
    -- Extract that c1 = c2 from cons equality
    injection heq

theorem uniqueness_7_4
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    (h_same_decode : decode ret1 = decode ret2)
    (h_decode_nil : ∀ (enc : List (Char × ℕ)), allPositiveCounts enc → decode enc = [] → enc = [])
    (h_decode_cons_nonempty : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → ¬decode ((c, n) :: rest) = [])
    (h_decode_head : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → (decode ((c, n) :: rest)).head? = some c)
    (h_replicate_append_eq : ∀ (c1 c2 : Char) (n1 n2 : ℕ) (rest1 rest2 : List Char), 0 < n1 → 0 < n2 → List.replicate n1 c1 ++ rest1 = List.replicate n2 c2 ++ rest2 → c1 = c2)
    : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((c, n) :: rest) → noConsecutiveSameChar ((c, n) :: rest) → List.takeWhile (fun x ↦ x == c) (decode ((c, n) :: rest)) = List.replicate n c := by
  intro c n rest hpos hnocons
  unfold decode
  simp only [List.flatMap_cons]
  have hn : n > 0 := by
    unfold allPositiveCounts at hpos
    have := hpos (c, n) (by simp)
    exact this
  rw [List.takeWhile_append]
  have htake_repl : List.takeWhile (fun x => x == c) (List.replicate n c) = List.replicate n c := by
    rw [List.takeWhile_replicate]
    simp [beq_self_eq_true]
  rw [htake_repl]
  simp only [List.length_replicate, ↓reduceIte]
  cases rest with
  | nil =>
    simp [List.flatMap]
  | cons p rest' =>
    obtain ⟨c', m⟩ := p
    have hm : m > 0 := by
      unfold allPositiveCounts at hpos
      have := hpos (c', m) (by simp)
      exact this
    have hne : c ≠ c' := by
      unfold noConsecutiveSameChar at hnocons
      have := hnocons 0 (by simp)
      simp at this
      exact this
    simp only [List.flatMap_cons]
    have htakeWhile_nil : List.takeWhile (fun x => x == c) (List.replicate m c' ++ List.flatMap (fun p => List.replicate p.2 p.1) rest') = [] := by
      cases m with
      | zero => omega
      | succ m' =>
        simp only [List.replicate_succ, List.cons_append]
        rw [List.takeWhile_cons_of_neg]
        simp only [beq_iff_eq]
        exact fun h => hne h.symm
    rw [htakeWhile_nil]
    simp

theorem uniqueness_7_6
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    (h_same_decode : decode ret1 = decode ret2)
    (h_decode_nil : ∀ (enc : List (Char × ℕ)), allPositiveCounts enc → decode enc = [] → enc = [])
    (h_count_leading : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((c, n) :: rest) → noConsecutiveSameChar ((c, n) :: rest) → List.takeWhile (fun x ↦ x == c) (decode ((c, n) :: rest)) = List.replicate n c)
    (h_takeWhile_eq_implies_count_eq : ∀ (c : Char) (n1 n2 : ℕ) (rest1 rest2 : List (Char × ℕ)), allPositiveCounts ((c, n1) :: rest1) → noConsecutiveSameChar ((c, n1) :: rest1) → allPositiveCounts ((c, n2) :: rest2) → noConsecutiveSameChar ((c, n2) :: rest2) → decode ((c, n1) :: rest1) = decode ((c, n2) :: rest2) → n1 = n2)
    (h_decode_cons_eq_implies_rest_eq : ∀ (c : Char) (n : ℕ) (rest1 rest2 : List (Char × ℕ)), decode ((c, n) :: rest1) = decode ((c, n) :: rest2) → decode rest1 = decode rest2)
    (h_decode_cons_nonempty : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → ¬decode ((c, n) :: rest) = [])
    (h_decode_head : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → (decode ((c, n) :: rest)).head? = some c)
    (h_replicate_append_eq : ∀ (c1 c2 : Char) (n1 n2 : ℕ) (rest1 rest2 : List Char), 0 < n1 → 0 < n2 → List.replicate n1 c1 ++ rest1 = List.replicate n2 c2 ++ rest2 → c1 = c2)
    : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((a, b) :: rest) → allPositiveCounts rest := by
    intro a b rest h
    unfold allPositiveCounts at h ⊢
    intro p hp
    apply h
    exact List.mem_cons_of_mem (a, b) hp

theorem uniqueness_7_7
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    (h_same_decode : decode ret1 = decode ret2)
    (h_decode_nil : ∀ (enc : List (Char × ℕ)), allPositiveCounts enc → decode enc = [] → enc = [])
    (h_count_leading : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((c, n) :: rest) → noConsecutiveSameChar ((c, n) :: rest) → List.takeWhile (fun x ↦ x == c) (decode ((c, n) :: rest)) = List.replicate n c)
    (h_takeWhile_eq_implies_count_eq : ∀ (c : Char) (n1 n2 : ℕ) (rest1 rest2 : List (Char × ℕ)), allPositiveCounts ((c, n1) :: rest1) → noConsecutiveSameChar ((c, n1) :: rest1) → allPositiveCounts ((c, n2) :: rest2) → noConsecutiveSameChar ((c, n2) :: rest2) → decode ((c, n1) :: rest1) = decode ((c, n2) :: rest2) → n1 = n2)
    (h_decode_cons_eq_implies_rest_eq : ∀ (c : Char) (n : ℕ) (rest1 rest2 : List (Char × ℕ)), decode ((c, n) :: rest1) = decode ((c, n) :: rest2) → decode rest1 = decode rest2)
    (h_decode_cons_nonempty : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → ¬decode ((c, n) :: rest) = [])
    (h_decode_head : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → (decode ((c, n) :: rest)).head? = some c)
    (h_replicate_append_eq : ∀ (c1 c2 : Char) (n1 n2 : ℕ) (rest1 rest2 : List Char), 0 < n1 → 0 < n2 → List.replicate n1 c1 ++ rest1 = List.replicate n2 c2 ++ rest2 → c1 = c2)
    (h_pos_tail : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((a, b) :: rest) → allPositiveCounts rest)
    : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), noConsecutiveSameChar ((a, b) :: rest) → noConsecutiveSameChar rest := by
  intro a b rest h
  unfold noConsecutiveSameChar at *
  intro i hi
  have hi' : (i + 1) + 1 < ((a, b) :: rest).length := by
    simp [List.length_cons]
    omega
  have := h (i + 1) hi'
  simp only [List.getElem!_cons_succ] at this
  exact this

theorem uniqueness_7_8
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    (h_same_decode : decode ret1 = decode ret2)
    (h_decode_nil : ∀ (enc : List (Char × ℕ)), allPositiveCounts enc → decode enc = [] → enc = [])
    (h_count_leading : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((c, n) :: rest) → noConsecutiveSameChar ((c, n) :: rest) → List.takeWhile (fun x ↦ x == c) (decode ((c, n) :: rest)) = List.replicate n c)
    (h_takeWhile_eq_implies_count_eq : ∀ (c : Char) (n1 n2 : ℕ) (rest1 rest2 : List (Char × ℕ)), allPositiveCounts ((c, n1) :: rest1) → noConsecutiveSameChar ((c, n1) :: rest1) → allPositiveCounts ((c, n2) :: rest2) → noConsecutiveSameChar ((c, n2) :: rest2) → decode ((c, n1) :: rest1) = decode ((c, n2) :: rest2) → n1 = n2)
    (h_decode_cons_eq_implies_rest_eq : ∀ (c : Char) (n : ℕ) (rest1 rest2 : List (Char × ℕ)), decode ((c, n) :: rest1) = decode ((c, n) :: rest2) → decode rest1 = decode rest2)
    (h_decode_cons_nonempty : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → ¬decode ((c, n) :: rest) = [])
    (h_decode_head : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → (decode ((c, n) :: rest)).head? = some c)
    (h_replicate_append_eq : ∀ (c1 c2 : Char) (n1 n2 : ℕ) (rest1 rest2 : List Char), 0 < n1 → 0 < n2 → List.replicate n1 c1 ++ rest1 = List.replicate n2 c2 ++ rest2 → c1 = c2)
    (h_pos_tail : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((a, b) :: rest) → allPositiveCounts rest)
    (h_nocons_tail : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), noConsecutiveSameChar ((a, b) :: rest) → noConsecutiveSameChar rest)
    : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((a, b) :: rest) → 0 < b := by
    intro a b rest h_pos
    unfold allPositiveCounts at h_pos
    have h_mem : (a, b) ∈ (a, b) :: rest := List.mem_cons_self
    exact h_pos (a, b) h_mem

theorem uniqueness_7_9
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    (h_same_decode : decode ret1 = decode ret2)
    (h_decode_nil : ∀ (enc : List (Char × ℕ)), allPositiveCounts enc → decode enc = [] → enc = [])
    (h_count_leading : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((c, n) :: rest) → noConsecutiveSameChar ((c, n) :: rest) → List.takeWhile (fun x ↦ x == c) (decode ((c, n) :: rest)) = List.replicate n c)
    (h_takeWhile_eq_implies_count_eq : ∀ (c : Char) (n1 n2 : ℕ) (rest1 rest2 : List (Char × ℕ)), allPositiveCounts ((c, n1) :: rest1) → noConsecutiveSameChar ((c, n1) :: rest1) → allPositiveCounts ((c, n2) :: rest2) → noConsecutiveSameChar ((c, n2) :: rest2) → decode ((c, n1) :: rest1) = decode ((c, n2) :: rest2) → n1 = n2)
    (h_decode_cons_eq_implies_rest_eq : ∀ (c : Char) (n : ℕ) (rest1 rest2 : List (Char × ℕ)), decode ((c, n) :: rest1) = decode ((c, n) :: rest2) → decode rest1 = decode rest2)
    (p1 : Char × ℕ)
    (rest1 : List (Char × ℕ))
    (ih : ∀ (enc2 : List (Char × ℕ)), allPositiveCounts rest1 → noConsecutiveSameChar rest1 → allPositiveCounts enc2 → noConsecutiveSameChar enc2 → decode rest1 = decode enc2 → rest1 = enc2)
    (enc2 : List (Char × ℕ))
    (hpos1 : allPositiveCounts (p1 :: rest1))
    (hnocons1 : noConsecutiveSameChar (p1 :: rest1))
    (p2 : Char × ℕ)
    (rest2 : List (Char × ℕ))
    (hpos2 : allPositiveCounts (p2 :: rest2))
    (hnocons2 : noConsecutiveSameChar (p2 :: rest2))
    (hdec_eq : decode (p1 :: rest1) = decode (p2 :: rest2))
    (h_decode_cons_nonempty : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → ¬decode ((c, n) :: rest) = [])
    (h_decode_head : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → (decode ((c, n) :: rest)).head? = some c)
    (h_replicate_append_eq : ∀ (c1 c2 : Char) (n1 n2 : ℕ) (rest1 rest2 : List Char), 0 < n1 → 0 < n2 → List.replicate n1 c1 ++ rest1 = List.replicate n2 c2 ++ rest2 → c1 = c2)
    (h_pos_tail : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((a, b) :: rest) → allPositiveCounts rest)
    (h_nocons_tail : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), noConsecutiveSameChar ((a, b) :: rest) → noConsecutiveSameChar rest)
    (h_pos_head : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((a, b) :: rest) → 0 < b)
    (h_p1_pos : 0 < p1.2)
    (h_p2_pos : 0 < p2.2)
    : p1.1 = p2.1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_7_10
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    (h_same_decode : decode ret1 = decode ret2)
    (h_decode_nil : ∀ (enc : List (Char × ℕ)), allPositiveCounts enc → decode enc = [] → enc = [])
    (h_count_leading : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((c, n) :: rest) → noConsecutiveSameChar ((c, n) :: rest) → List.takeWhile (fun x ↦ x == c) (decode ((c, n) :: rest)) = List.replicate n c)
    (h_takeWhile_eq_implies_count_eq : ∀ (c : Char) (n1 n2 : ℕ) (rest1 rest2 : List (Char × ℕ)), allPositiveCounts ((c, n1) :: rest1) → noConsecutiveSameChar ((c, n1) :: rest1) → allPositiveCounts ((c, n2) :: rest2) → noConsecutiveSameChar ((c, n2) :: rest2) → decode ((c, n1) :: rest1) = decode ((c, n2) :: rest2) → n1 = n2)
    (h_decode_cons_eq_implies_rest_eq : ∀ (c : Char) (n : ℕ) (rest1 rest2 : List (Char × ℕ)), decode ((c, n) :: rest1) = decode ((c, n) :: rest2) → decode rest1 = decode rest2)
    (p1 : Char × ℕ)
    (rest1 : List (Char × ℕ))
    (ih : ∀ (enc2 : List (Char × ℕ)), allPositiveCounts rest1 → noConsecutiveSameChar rest1 → allPositiveCounts enc2 → noConsecutiveSameChar enc2 → decode rest1 = decode enc2 → rest1 = enc2)
    (enc2 : List (Char × ℕ))
    (hpos1 : allPositiveCounts (p1 :: rest1))
    (hnocons1 : noConsecutiveSameChar (p1 :: rest1))
    (p2 : Char × ℕ)
    (rest2 : List (Char × ℕ))
    (hpos2 : allPositiveCounts (p2 :: rest2))
    (hnocons2 : noConsecutiveSameChar (p2 :: rest2))
    (hdec_eq : decode (p1 :: rest1) = decode (p2 :: rest2))
    (h_c_eq : p1.1 = p2.1)
    (h_decode_cons_nonempty : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → ¬decode ((c, n) :: rest) = [])
    (h_decode_head : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → (decode ((c, n) :: rest)).head? = some c)
    (h_replicate_append_eq : ∀ (c1 c2 : Char) (n1 n2 : ℕ) (rest1 rest2 : List Char), 0 < n1 → 0 < n2 → List.replicate n1 c1 ++ rest1 = List.replicate n2 c2 ++ rest2 → c1 = c2)
    (h_pos_tail : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((a, b) :: rest) → allPositiveCounts rest)
    (h_nocons_tail : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), noConsecutiveSameChar ((a, b) :: rest) → noConsecutiveSameChar rest)
    (h_pos_head : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((a, b) :: rest) → 0 < b)
    (h_p1_pos : 0 < p1.2)
    (h_p2_pos : 0 < p2.2)
    : p1.2 = p2.2 := by
    have hp1_eta : p1 = (p1.1, p1.2) := (Prod.eta p1).symm
    have hp2_eta : p2 = (p2.1, p2.2) := (Prod.eta p2).symm
    have h_c_eq' : p2.1 = p1.1 := h_c_eq.symm
    rw [hp1_eta] at hpos1 hnocons1 hdec_eq
    rw [hp2_eta] at hpos2 hnocons2 hdec_eq
    rw [h_c_eq'] at hpos2 hnocons2 hdec_eq
    exact h_takeWhile_eq_implies_count_eq p1.1 p1.2 p2.2 rest1 rest2 hpos1 hnocons1 hpos2 hnocons2 hdec_eq

theorem uniqueness_7_11
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    (h_same_decode : decode ret1 = decode ret2)
    (h_decode_nil : ∀ (enc : List (Char × ℕ)), allPositiveCounts enc → decode enc = [] → enc = [])
    (h_count_leading : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((c, n) :: rest) → noConsecutiveSameChar ((c, n) :: rest) → List.takeWhile (fun x ↦ x == c) (decode ((c, n) :: rest)) = List.replicate n c)
    (h_takeWhile_eq_implies_count_eq : ∀ (c : Char) (n1 n2 : ℕ) (rest1 rest2 : List (Char × ℕ)), allPositiveCounts ((c, n1) :: rest1) → noConsecutiveSameChar ((c, n1) :: rest1) → allPositiveCounts ((c, n2) :: rest2) → noConsecutiveSameChar ((c, n2) :: rest2) → decode ((c, n1) :: rest1) = decode ((c, n2) :: rest2) → n1 = n2)
    (h_decode_cons_eq_implies_rest_eq : ∀ (c : Char) (n : ℕ) (rest1 rest2 : List (Char × ℕ)), decode ((c, n) :: rest1) = decode ((c, n) :: rest2) → decode rest1 = decode rest2)
    (p1 : Char × ℕ)
    (rest1 : List (Char × ℕ))
    (ih : ∀ (enc2 : List (Char × ℕ)), allPositiveCounts rest1 → noConsecutiveSameChar rest1 → allPositiveCounts enc2 → noConsecutiveSameChar enc2 → decode rest1 = decode enc2 → rest1 = enc2)
    (enc2 : List (Char × ℕ))
    (hpos1 : allPositiveCounts (p1 :: rest1))
    (hnocons1 : noConsecutiveSameChar (p1 :: rest1))
    (p2 : Char × ℕ)
    (rest2 : List (Char × ℕ))
    (hpos2 : allPositiveCounts (p2 :: rest2))
    (hnocons2 : noConsecutiveSameChar (p2 :: rest2))
    (hdec_eq : decode (p1 :: rest1) = decode (p2 :: rest2))
    (h_c_eq : p1.1 = p2.1)
    (h_n_eq : p1.2 = p2.2)
    (h_p_eq : p1 = p2)
    (h_rest_pos1 : allPositiveCounts rest1)
    (h_rest_pos2 : allPositiveCounts rest2)
    (h_rest_nocons1 : noConsecutiveSameChar rest1)
    (h_rest_nocons2 : noConsecutiveSameChar rest2)
    (h_decode_cons_nonempty : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → ¬decode ((c, n) :: rest) = [])
    (h_decode_head : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → (decode ((c, n) :: rest)).head? = some c)
    (h_replicate_append_eq : ∀ (c1 c2 : Char) (n1 n2 : ℕ) (rest1 rest2 : List Char), 0 < n1 → 0 < n2 → List.replicate n1 c1 ++ rest1 = List.replicate n2 c2 ++ rest2 → c1 = c2)
    (h_pos_tail : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((a, b) :: rest) → allPositiveCounts rest)
    (h_nocons_tail : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), noConsecutiveSameChar ((a, b) :: rest) → noConsecutiveSameChar rest)
    (h_pos_head : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((a, b) :: rest) → 0 < b)
    (h_p1_pos : 0 < p1.2)
    (h_p2_pos : 0 < p2.2)
    : decode rest1 = decode rest2 := by
    subst h_p_eq
    have p1_eta : p1 = (p1.1, p1.2) := (Prod.eta p1).symm
    rw [p1_eta] at hdec_eq
    exact h_decode_cons_eq_implies_rest_eq p1.1 p1.2 rest1 rest2 hdec_eq

theorem uniqueness_7_12
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    (h_same_decode : decode ret1 = decode ret2)
    (h_decode_nil : ∀ (enc : List (Char × ℕ)), allPositiveCounts enc → decode enc = [] → enc = [])
    (h_count_leading : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((c, n) :: rest) → noConsecutiveSameChar ((c, n) :: rest) → List.takeWhile (fun x ↦ x == c) (decode ((c, n) :: rest)) = List.replicate n c)
    (h_takeWhile_eq_implies_count_eq : ∀ (c : Char) (n1 n2 : ℕ) (rest1 rest2 : List (Char × ℕ)), allPositiveCounts ((c, n1) :: rest1) → noConsecutiveSameChar ((c, n1) :: rest1) → allPositiveCounts ((c, n2) :: rest2) → noConsecutiveSameChar ((c, n2) :: rest2) → decode ((c, n1) :: rest1) = decode ((c, n2) :: rest2) → n1 = n2)
    (h_decode_cons_eq_implies_rest_eq : ∀ (c : Char) (n : ℕ) (rest1 rest2 : List (Char × ℕ)), decode ((c, n) :: rest1) = decode ((c, n) :: rest2) → decode rest1 = decode rest2)
    (p1 : Char × ℕ)
    (rest1 : List (Char × ℕ))
    (ih : ∀ (enc2 : List (Char × ℕ)), allPositiveCounts rest1 → noConsecutiveSameChar rest1 → allPositiveCounts enc2 → noConsecutiveSameChar enc2 → decode rest1 = decode enc2 → rest1 = enc2)
    (enc2 : List (Char × ℕ))
    (hpos1 : allPositiveCounts (p1 :: rest1))
    (hnocons1 : noConsecutiveSameChar (p1 :: rest1))
    (p2 : Char × ℕ)
    (rest2 : List (Char × ℕ))
    (hpos2 : allPositiveCounts (p2 :: rest2))
    (hnocons2 : noConsecutiveSameChar (p2 :: rest2))
    (hdec_eq : decode (p1 :: rest1) = decode (p2 :: rest2))
    (h_c_eq : p1.1 = p2.1)
    (h_n_eq : p1.2 = p2.2)
    (h_p_eq : p1 = p2)
    (h_rest_pos1 : allPositiveCounts rest1)
    (h_rest_pos2 : allPositiveCounts rest2)
    (h_rest_nocons1 : noConsecutiveSameChar rest1)
    (h_rest_nocons2 : noConsecutiveSameChar rest2)
    (h_rest_dec_eq : decode rest1 = decode rest2)
    (h_decode_cons_nonempty : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → ¬decode ((c, n) :: rest) = [])
    (h_decode_head : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → (decode ((c, n) :: rest)).head? = some c)
    (h_replicate_append_eq : ∀ (c1 c2 : Char) (n1 n2 : ℕ) (rest1 rest2 : List Char), 0 < n1 → 0 < n2 → List.replicate n1 c1 ++ rest1 = List.replicate n2 c2 ++ rest2 → c1 = c2)
    (h_pos_tail : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((a, b) :: rest) → allPositiveCounts rest)
    (h_nocons_tail : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), noConsecutiveSameChar ((a, b) :: rest) → noConsecutiveSameChar rest)
    (h_pos_head : ∀ (a : Char) (b : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((a, b) :: rest) → 0 < b)
    (h_p1_pos : 0 < p1.2)
    (h_p2_pos : 0 < p2.2)
    : rest1 = rest2 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_7_5
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    (h_same_decode : decode ret1 = decode ret2)
    (h_decode_nil : ∀ (enc : List (Char × ℕ)), allPositiveCounts enc → decode enc = [] → enc = [])
    (h_count_leading : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((c, n) :: rest) → noConsecutiveSameChar ((c, n) :: rest) → List.takeWhile (fun x ↦ x == c) (decode ((c, n) :: rest)) = List.replicate n c)
    (h_decode_cons_nonempty : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → ¬decode ((c, n) :: rest) = [])
    (h_decode_head : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), 0 < n → (decode ((c, n) :: rest)).head? = some c)
    (h_replicate_append_eq : ∀ (c1 c2 : Char) (n1 n2 : ℕ) (rest1 rest2 : List Char), 0 < n1 → 0 < n2 → List.replicate n1 c1 ++ rest1 = List.replicate n2 c2 ++ rest2 → c1 = c2)
    : ∀ (c : Char) (n1 n2 : ℕ) (rest1 rest2 : List (Char × ℕ)), allPositiveCounts ((c, n1) :: rest1) → noConsecutiveSameChar ((c, n1) :: rest1) → allPositiveCounts ((c, n2) :: rest2) → noConsecutiveSameChar ((c, n2) :: rest2) → decode ((c, n1) :: rest1) = decode ((c, n2) :: rest2) → n1 = n2 := by
    sorry

theorem uniqueness_7
    (s : String)
    (_hpre : precondition s)
    (ret1 : List (Char × ℕ))
    (ret2 : List (Char × ℕ))
    (hpost1 : postcondition s ret1)
    (hpost2 : postcondition s ret2)
    (h1_pos : allPositiveCounts ret1)
    (h1_nocons : noConsecutiveSameChar ret1)
    (h1_decode : decode ret1 = s.data)
    (h2_pos : allPositiveCounts ret2)
    (h2_nocons : noConsecutiveSameChar ret2)
    (h2_decode : decode ret2 = s.data)
    (h_same_decode : decode ret1 = decode ret2)
    : ∀ (enc1 enc2 : List (Char × ℕ)), allPositiveCounts enc1 → noConsecutiveSameChar enc1 → allPositiveCounts enc2 → noConsecutiveSameChar enc2 → decode enc1 = decode enc2 → enc1 = enc2 := by
    have h_decode_nil : ∀ enc, allPositiveCounts enc → decode enc = [] → enc = [] := by (try simp at *; expose_names); exact (uniqueness_7_0 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode h_same_decode); done
    have h_decode_cons_nonempty : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), n > 0 → decode ((c, n) :: rest) ≠ [] := by (try simp at *; expose_names); exact (uniqueness_7_1 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode h_same_decode h_decode_nil); done
    have h_decode_head : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)) (hn : n > 0), (decode ((c, n) :: rest)).head? = some c := by (try simp at *; expose_names); exact (uniqueness_7_2 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode h_same_decode h_decode_nil h_decode_cons_nonempty); done
    have h_replicate_append_eq : ∀ (c1 c2 : Char) (n1 n2 : ℕ) (rest1 rest2 : List Char), n1 > 0 → n2 > 0 → List.replicate n1 c1 ++ rest1 = List.replicate n2 c2 ++ rest2 → c1 = c2 := by (try simp at *; expose_names); exact (uniqueness_7_3 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode h_same_decode h_decode_nil h_decode_cons_nonempty h_decode_head); done
    have h_count_leading : ∀ (c : Char) (n : ℕ) (rest : List (Char × ℕ)), allPositiveCounts ((c, n) :: rest) → noConsecutiveSameChar ((c, n) :: rest) → (decode ((c, n) :: rest)).takeWhile (· == c) = List.replicate n c := by (try simp at *; expose_names); exact (uniqueness_7_4 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode h_same_decode h_decode_nil h_decode_cons_nonempty h_decode_head h_replicate_append_eq); done
    have h_takeWhile_eq_implies_count_eq : ∀ (c : Char) (n1 n2 : ℕ) (rest1 rest2 : List (Char × ℕ)), allPositiveCounts ((c, n1) :: rest1) → noConsecutiveSameChar ((c, n1) :: rest1) → allPositiveCounts ((c, n2) :: rest2) → noConsecutiveSameChar ((c, n2) :: rest2) → decode ((c, n1) :: rest1) = decode ((c, n2) :: rest2) → n1 = n2 := by (try simp at *; expose_names); exact (uniqueness_7_5 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode h_same_decode h_decode_nil h_count_leading h_decode_cons_nonempty h_decode_head h_replicate_append_eq); done
    have h_decode_cons_eq_implies_rest_eq : ∀ (c : Char) (n : ℕ) (rest1 rest2 : List (Char × ℕ)), decode ((c, n) :: rest1) = decode ((c, n) :: rest2) → decode rest1 = decode rest2 := by (try simp at *; expose_names); exact (fun c n rest1 rest2 a ↦ List.append_cancel_left a); done
    have h_pos_tail : ∀ (p : Char × ℕ) (rest : List (Char × ℕ)), allPositiveCounts (p :: rest) → allPositiveCounts rest := by (try simp at *; expose_names); exact (uniqueness_7_6 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode h_same_decode h_decode_nil h_count_leading h_takeWhile_eq_implies_count_eq h_decode_cons_eq_implies_rest_eq h_decode_cons_nonempty h_decode_head h_replicate_append_eq); done
    have h_nocons_tail : ∀ (p : Char × ℕ) (rest : List (Char × ℕ)), noConsecutiveSameChar (p :: rest) → noConsecutiveSameChar rest := by (try simp at *; expose_names); exact (uniqueness_7_7 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode h_same_decode h_decode_nil h_count_leading h_takeWhile_eq_implies_count_eq h_decode_cons_eq_implies_rest_eq h_decode_cons_nonempty h_decode_head h_replicate_append_eq h_pos_tail); done
    have h_pos_head : ∀ (p : Char × ℕ) (rest : List (Char × ℕ)), allPositiveCounts (p :: rest) → p.2 > 0 := by (try simp at *; expose_names); exact (uniqueness_7_8 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode h_same_decode h_decode_nil h_count_leading h_takeWhile_eq_implies_count_eq h_decode_cons_eq_implies_rest_eq h_decode_cons_nonempty h_decode_head h_replicate_append_eq h_pos_tail h_nocons_tail); done
    intro enc1 enc2 hpos1 hnocons1 hpos2 hnocons2 hdec_eq
    induction enc1 generalizing enc2 with
    | nil =>
      have h_dec1_nil : decode [] = [] := by (try simp at *; expose_names); exact rfl; done
      have h_dec2_eq_nil : decode enc2 = [] := by (try simp at *; expose_names); exact (id (Eq.symm hdec_eq)); done
      exact (h_decode_nil enc2 hpos2 h_dec2_eq_nil).symm
    | cons p1 rest1 ih =>
      match enc2 with
      | [] =>
        have h_dec2_nil : decode [] = [] := by (try simp at *; expose_names); exact rfl; done
        have h_dec1_eq_nil : decode (p1 :: rest1) = [] := by (try simp at *; expose_names); exact (hdec_eq); done
        have h_p1_pos : p1.2 > 0 := by (try simp at *; expose_names); exact (h_pos_head p1.1 p1.2 rest1 hpos1); done
        have h_dec1_nonempty : decode (p1 :: rest1) ≠ [] := by (try simp at *; expose_names); exact (h_decode_cons_nonempty p1.1 p1.2 rest1 (h_pos_head p1.1 p1.2 rest1 hpos1)); done
        exact absurd h_dec1_eq_nil h_dec1_nonempty
      | p2 :: rest2 =>
        have h_p1_pos : p1.2 > 0 := by (try simp at *; expose_names); exact (h_pos_head p1.1 p1.2 rest1 hpos1); done
        have h_p2_pos : p2.2 > 0 := by (try simp at *; expose_names); exact (h_pos_head p2.1 p2.2 rest2 hpos2); done
        have h_c_eq : p1.1 = p2.1 := by (try simp at *; expose_names); exact (uniqueness_7_9 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode h_same_decode h_decode_nil h_count_leading h_takeWhile_eq_implies_count_eq h_decode_cons_eq_implies_rest_eq p1 rest1 ih enc2 hpos1 hnocons1 p2 rest2 hpos2 hnocons2 hdec_eq h_decode_cons_nonempty h_decode_head h_replicate_append_eq h_pos_tail h_nocons_tail h_pos_head h_p1_pos h_p2_pos); done
        have h_n_eq : p1.2 = p2.2 := by (try simp at *; expose_names); exact (uniqueness_7_10 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode h_same_decode h_decode_nil h_count_leading h_takeWhile_eq_implies_count_eq h_decode_cons_eq_implies_rest_eq p1 rest1 ih enc2 hpos1 hnocons1 p2 rest2 hpos2 hnocons2 hdec_eq h_c_eq h_decode_cons_nonempty h_decode_head h_replicate_append_eq h_pos_tail h_nocons_tail h_pos_head h_p1_pos h_p2_pos); done
        have h_p_eq : p1 = p2 := by (try simp at *; expose_names); exact Prod.ext h_c_eq h_n_eq; done
        have h_rest_pos1 : allPositiveCounts rest1 := by (try simp at *; expose_names); exact (h_pos_tail p1.1 p1.2 rest1 hpos1); done
        have h_rest_pos2 : allPositiveCounts rest2 := by (try simp at *; expose_names); exact (h_pos_tail p2.1 p2.2 rest2 hpos2); done
        have h_rest_nocons1 : noConsecutiveSameChar rest1 := by (try simp at *; expose_names); exact (h_nocons_tail p1.1 p1.2 rest1 hnocons1); done
        have h_rest_nocons2 : noConsecutiveSameChar rest2 := by (try simp at *; expose_names); exact (h_nocons_tail p2.1 p2.2 rest2 hnocons2); done
        have h_rest_dec_eq : decode rest1 = decode rest2 := by (try simp at *; expose_names); exact (uniqueness_7_11 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode h_same_decode h_decode_nil h_count_leading h_takeWhile_eq_implies_count_eq h_decode_cons_eq_implies_rest_eq p1 rest1 ih enc2 hpos1 hnocons1 p2 rest2 hpos2 hnocons2 hdec_eq h_c_eq h_n_eq h_p_eq h_rest_pos1 h_rest_pos2 h_rest_nocons1 h_rest_nocons2 h_decode_cons_nonempty h_decode_head h_replicate_append_eq h_pos_tail h_nocons_tail h_pos_head h_p1_pos h_p2_pos); done
        have h_rest_eq : rest1 = rest2 := by (try simp at *; expose_names); exact (uniqueness_7_12 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode h_same_decode h_decode_nil h_count_leading h_takeWhile_eq_implies_count_eq h_decode_cons_eq_implies_rest_eq p1 rest1 ih enc2 hpos1 hnocons1 p2 rest2 hpos2 hnocons2 hdec_eq h_c_eq h_n_eq h_p_eq h_rest_pos1 h_rest_pos2 h_rest_nocons1 h_rest_nocons2 h_rest_dec_eq h_decode_cons_nonempty h_decode_head h_replicate_append_eq h_pos_tail h_nocons_tail h_pos_head h_p1_pos h_p2_pos); done
        simp only [h_p_eq, h_rest_eq]

theorem uniqueness (s : String):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- Extract the three ensures conditions from both postconditions
  have h1_pos : allPositiveCounts ret1 := by (try simp at *; expose_names); exact (uniqueness_0 s _hpre ret1 ret2 hpost1 hpost2); done
  have h1_nocons : noConsecutiveSameChar ret1 := by (try simp at *; expose_names); exact (uniqueness_1 s _hpre ret1 ret2 hpost1 hpost2 h1_pos); done
  have h1_decode : decode ret1 = s.toList := by (try simp at *; expose_names); exact (uniqueness_2 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons); done
  have h2_pos : allPositiveCounts ret2 := by (try simp at *; expose_names); exact (uniqueness_3 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode); done
  have h2_nocons : noConsecutiveSameChar ret2 := by (try simp at *; expose_names); exact (uniqueness_4 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos); done
  have h2_decode : decode ret2 = s.toList := by (try simp at *; expose_names); exact (uniqueness_5 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons); done
  -- Both decode to the same list
  have h_same_decode : decode ret1 = decode ret2 := by (try simp at *; expose_names); exact (uniqueness_6 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode); done
  -- Key lemma: run-length encoding with these constraints is unique
  -- We prove this by showing that the encoding is determined by the decoded string
  -- when we require positive counts and no consecutive same characters
  have h_unique_encoding : ∀ (enc1 enc2 : List (Char × Nat)),
    allPositiveCounts enc1 →
    noConsecutiveSameChar enc1 →
    allPositiveCounts enc2 →
    noConsecutiveSameChar enc2 →
    decode enc1 = decode enc2 →
    enc1 = enc2 := by (try simp at *; expose_names); exact (uniqueness_7 s _hpre ret1 ret2 hpost1 hpost2 h1_pos h1_nocons h1_decode h2_pos h2_nocons h2_decode h_same_decode); done
  -- Apply the uniqueness lemma
  exact h_unique_encoding ret1 ret2 h1_pos h1_nocons h2_pos h2_nocons h_same_decode
end Proof
