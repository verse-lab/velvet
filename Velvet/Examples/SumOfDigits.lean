import Velvet

/-!
# Sum of digits

Port of `velvet-dev/Velvet/Examples/SumOfDigits.lean`: repeatedly peel off the last
decimal digit, maintaining `sum + sumDigits n = sumDigits number`.
-/

open Std.WP

/-- Recursive specification of the digit sum. -/
@[grind ]
def sumDigits (n : Nat) : Nat :=
  if n = 0 then 0 else n % 10 + sumDigits (n / 10)

-- The loop peels off one digit per iteration; the measure is `n` itself.
method sumOfDigits (number : Nat)
  returns (sum : Nat)
  ensures sum_is: sum = sumDigits number
do
  let mut sum := 0
  let mut n := number
  while' loop_cond: n > 0
    invariant digit_sum: sum + sumDigits n = sumDigits number
    invariant sum_nonneg: 0 ≤ sum
    decreasing by_n: n
    done_with zero: n = 0
  do
    let digit := n % 10
    sum := sum + digit
    n := n / 10
  return sum

prove_correct sumOfDigits by
  vcgen_ [sumOfDigits] with finish
