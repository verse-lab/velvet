module

public import Velvet
public meta import Velvet

open Std.Internal.Do

@[grind →]
public theorem sq_ge_four {d : Nat} (h : 2 ≤ d) : 4 ≤ d * d :=
  Nat.mul_le_mul h h

@[grind →]
public theorem two_mul_le_sq {i : Nat} (h : 2 ≤ i) : 2 * i ≤ i * i :=
  Nat.mul_le_mul_right i h

/-- A nontrivial divisor whose square is at most `n` yields a smaller nontrivial
divisor below `i` whenever `n < i * i`. -/
public theorem small_divisor_exists {n d i : Nat} (hd2 : 2 ≤ d) (hdn : n % d = 0)
    (hsq : d * d ≤ n) (hscan : n < i * i) (_hi : 2 ≤ i) :
    ∃ e, 2 ≤ e ∧ e < i ∧ n % e = 0 := by
  rcases Nat.lt_or_ge d i with hlt | hge
  · exact ⟨d, hd2, hlt, hdn⟩
  · -- the co-divisor `n / d` is an even smaller nontrivial divisor
    have hdmul : d * (n / d) = n := by
      have h := Nat.div_add_mod n d
      omega
    have hk : (0 : Nat) < d := by omega
    refine ⟨n / d, ?_, ?_, ?_⟩
    · exact Nat.le_trans hd2 ((Nat.le_div_iff_mul_le (x := d) (y := n) (k := d) hk).mpr hsq)
    · have hid : i * i ≤ d * i := Nat.mul_le_mul hge (Nat.le_refl i)
      have hlt2 : n < i * d := by
        calc n < i * i := hscan
          _ ≤ d * i := hid
          _ = i * d := Nat.mul_comm d i
      exact (Nat.div_lt_iff_lt_mul hk).mpr hlt2
    · have he : n % (n / d) = ((n / d) * d) % (n / d) := by
        congr 1
        rw [Nat.mul_comm]
        exact hdmul.symm
      rw [he]
      exact Nat.mul_mod_right _ _

method isNonPrime (n : Nat)
  returns (result : Bool)
  ensures result_iff: result = true ↔ (∃ d, 2 ≤ d ∧ d * d ≤ n ∧ n % d = 0)
do
  if n ≤ 1 then
    return false
  let mut i : Nat := 2
  let mut ret := false
  while' loop_cond: i * i ≤ n
    invariant i_lower: 2 ≤ i
    invariant ret_iff: ret = false ↔ (∀ d, 2 ≤ d ∧ d < i → n % d ≠ 0)
    invariant progress: (i - 1) * (i - 1) ≤ n
    decreasing by_bound: n + 1 - i
    done_with scanned: n < i * i
  do
    if n % i = 0 then
      ret := true
    else
      ret := ret
    i := i + 1
  return ret

prove_correct isNonPrime by
  velvet_vcgen [isNonPrime] with try finish
  case result_iff =>
    rename_i n
    cases ret
    · simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro d hd2 hdsq hdn
      obtain ⟨e, he2, hei, hen⟩ := small_divisor_exists hd2 hdn hdsq scanned i_lower
      exact (ret_iff.mp rfl) e ⟨he2, hei⟩ hen
    · simp only [true_iff]
      obtain ⟨d, hd2, hdi, hdn⟩ : ∃ d, 2 ≤ d ∧ d < i ∧ n % d = 0 := by
        apply Classical.byContradiction
        intro h
        have hall : ∀ d, 2 ≤ d ∧ d < i → n % d ≠ 0 := fun d hd hd0 => h ⟨d, hd.1, hd.2, hd0⟩
        exact Bool.noConfusion (ret_iff.mpr hall)
      have hle : d ≤ i - 1 := by omega
      have hdsq : d * d ≤ (i - 1) * (i - 1) := Nat.mul_le_mul hle hle
      exact ⟨d, hd2, by omega, hdn⟩
