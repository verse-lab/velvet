/* Problem Description
    sumOfDigits: compute the sum of the base-10 digits of a non-negative integer.
    Natural language breakdown:
    1. The input n is a natural number (a non-negative integer).
    2. Consider the canonical base-10 digit list of n given by Mathlib: `Nat.digits 10 n`.
       This list is in little-endian order (least-significant digit first).
    3. Each element of `Nat.digits 10 n` is a digit in the range 0..9.
    4. The output is the sum of these digits.
    5. In particular, for n = 0, the digit list is empty and the sum is 0.
    6. The result is a natural number.
*/

// Helper function to compute sum of digits
function sumDigits(n: nat): nat
  decreases n
{
  if n == 0 then 0 else (n % 10) + sumDigits(n / 10)
}

// No special precondition: input is already a Nat
predicate precondition(n: nat)
{
  true
}

// Postcondition: result is exactly the sum of the canonical base-10 digits
predicate postcondition(n: nat, result: nat)
{
  result == sumDigits(n)
}

method sumOfDigits(n: nat) returns (result: nat)
  requires precondition(n)
  ensures postcondition(n, result)
{
  var t := n;
  var s: nat := 0;

  while t > 0
    // Invariant: accumulator tracks the sum of digits already removed from `t`.
    // Initialization: `t = n`, so removed prefix is `[]` and sum is 0.
    // Preservation: writing `t = 10*q + r` with `r = t % 10`, `q = t / 10`, we add `r` to `s` and set `t := q`.
    // Sufficiency: on exit `t = 0`, the removed digits are exactly `Nat.digits 10 n`, hence `s` is their sum.
    invariant s + sumDigits(t) == sumDigits(n)
    decreases t
  {
    var d := t % 10;
    s := s + d;
    t := t / 10;
  }

  result := s;
}

