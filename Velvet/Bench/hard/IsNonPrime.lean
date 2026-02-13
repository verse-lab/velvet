import Velvet.Std
import Mathlib.Data.Nat.Prime.Defs

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

method IsNonPrime (n: Nat)
  return (result: Bool)
  ensures result ↔ ¬Nat.Prime n
  do
    if n ≤ 1 then
      return true
    let mut i: Nat := 2
    let mut ret: Bool := false
    while i * i ≤ n
    invariant 2 ≤ i
    invariant (ret = false ↔ ∀ d, 2 ≤ d ∧ d < i → n % d ≠ 0)
    invariant (i - 1) * (i - 1) ≤ n
    do
      if n % i = 0 then
        ret := true
      i := i + 1
    return ret

-- ------------------------------------------------
-- -- Program verification
-- ------------------------------------------------

attribute [grind] Nat.prime_def_le_sqrt Nat.dvd_iff_mod_eq_zero

prove_correct IsNonPrime by
  loom_solve; try simp_all
  rw [Nat.prime_def_le_sqrt]
  have hi : i - 1 = n.sqrt := by
    have H1 := Nat.le_sqrt.mpr invariant_3
    have H2 := Nat.sqrt_lt.mpr done_1
    grind
  constructor
  · aesop; use w; grind
  · cases ret_1 <;> grind
