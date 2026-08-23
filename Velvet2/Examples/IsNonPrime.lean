import Velvet2.Syntax
import Velvet2.VCGen.Frontend

open Std.Internal.Do

/-- A nontrivial divisor whose square is at most `n` yields a smaller nontrivial
divisor below `i` whenever `n < i * i`. -/
theorem small_divisor_exists {n d i : Nat} (hd2 : 2 ≤ d) (hdn : n % d = 0)
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

set_option velvet.semantics.termination "partial" in
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
    done_with scanned: n < i * i
  do
    if n % i = 0 then
      ret := true
    else
      ret := ret
    i := i + 1
  return ret

prove_correct isNonPrime by
  vcgen_ [isNonPrime] simplifying_assumptions with try finish
  case result_iff =>
    rename_i n
    exact
      ⟨False.elim, fun ⟨d, hd2, hdsq, _⟩ => by
        have h4 : (4 : Nat) ≤ d * d := Nat.mul_le_mul hd2 hd2
        omega⟩
  case result_iff =>
    rename_i n i ret
    obtain ⟨hinv_of_false, hfalse_of_inv⟩ := ret_iff
    constructor
    · intro hb
      have hbf : ¬(ret = false) := by simp [hb]
      have hnotall : ¬ (∀ d, 2 ≤ d ∧ d < i → n % d ≠ 0) :=
        fun hall => hbf (hfalse_of_inv hall)
      obtain ⟨d, hd2, hdlt, hdvd⟩ : ∃ d, 2 ≤ d ∧ d < i ∧ n % d = 0 := by
        refine Classical.byContradiction fun hcon => hnotall (fun d hconj => ?_)
        cases hd0 : n % d with
        | zero => exact absurd ⟨d, hconj.1, hconj.2, hd0⟩ hcon
        | succ m => omega
      refine ⟨d, hd2, ?_, hdvd⟩
      have hle : d ≤ i - 1 := by omega
      have hsq : d * d ≤ (i - 1) * (i - 1) := Nat.mul_le_mul hle hle
      grind
    · rintro ⟨d, hd2, hdsq, hdvd⟩
      cases hb : ret with
      | true => exact rfl
      | false =>
          obtain ⟨e, he2, helt, hevd⟩ :=
            small_divisor_exists hd2 hdvd hdsq scanned i_lower
          exact absurd hevd ((hinv_of_false hb) e ⟨he2, helt⟩)
