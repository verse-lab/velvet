import CaseStudies.Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    ifPowerOfFour: Determine whether a natural number is a power of four
    Natural language breakdown:
    1. A natural number n is a power of four if there exists a natural number x such that n = 4^x
    2. Powers of four are: 1 (4^0), 4 (4^1), 16 (4^2), 64 (4^3), 256 (4^4), 1024 (4^5), ...
    3. 0 is NOT a power of four (there is no x such that 4^x = 0)
    4. 1 is a power of four (4^0 = 1)
    5. Numbers like 2, 3, 8, etc. are not powers of four
    6. The function returns true if n is a power of four, false otherwise

    Key observations:
    - 4^x is always positive for any natural x, so 0 is never a power of four
    - We need to check if n can be expressed as 4^x for some natural x
    - This is equivalent to checking if n = (2^2)^x = 2^(2x), i.e., n is a power of 2 with even exponent
-/

@[grind]
def isPowerOfFour (n : Nat) : Prop :=
  ∃ x : Nat, 4 ^ x = n

section Impl
method ifPowerOfFour (n: Nat)
  return (result: Bool)
  ensures result = true ↔ isPowerOfFour n
  do
    if n = 0 then
      return false
    else
      let mut current := n
      while current > 1 ∧ current % 4 = 0
        -- Invariant 1: current is positive (we started with n > 0 and only divide)
        invariant "current_pos" current > 0
        -- Invariant 2: n is a power of 4 iff current is a power of 4
        -- Initialization: current = n, so trivially holds
        -- Preservation: if current = 4^k and current % 4 = 0, then current/4 = 4^(k-1)
        -- Sufficiency: when current = 1, isPowerOfFour current holds (4^0 = 1)
        invariant "power_preserved" (isPowerOfFour n ↔ isPowerOfFour current)
        done_with current = 1 ∨ current % 4 ≠ 0
      do
        current := current / 4
      return current = 1
end Impl

section Proof
set_option maxHeartbeats 10000000

prove_correct ifPowerOfFour by
  loom_solve_async <;> simp at *
  · intro ⟨x, hx⟩; induction x <;> grind
  · constructor
    · intro h
      obtain ⟨y, hy⟩ := invariant_power_preserved.mp h
      cases y <;> grind
    · rintro ⟨y,hy⟩; rw [invariant_power_preserved]
      exists y+1; grind
  · constructor
    · intro; rw [invariant_power_preserved]
      exists 0; grind
    · cases done_1 <;> try grind
      intro h'
      have ⟨y,hy⟩: isPowerOfFour current := by grind
      cases y <;> grind
end Proof
