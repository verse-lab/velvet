// Problem Description
//   sumAndAverage: compute the sum and average of the first n natural numbers.
//   Natural language breakdown:
//   1. Input n is a natural number.
//   2. The sum is the sum of all natural numbers from 0 to n inclusive.
//   3. The sum satisfies Gauss' identity: 2 * sum = n * (n + 1).
//   4. The output sum is returned as an Int and must be nonnegative.
//   5. The average is a real (represented as real in Dafny) intended to represent sum / n.
//   6. Although the narrative says n is positive, the tests include n = 0.
//   7. For n = 0, the output is defined by the tests as (0, 0.0).
//   8. For n > 0, the average is defined using real division of the sum by n.

// Helper: closed-form Gauss sum as a Nat (this is specification-level, non-recursive).
// We use Nat arithmetic; for n=0 this yields 0.
function gaussSumNat(n: nat): nat
{
  n * (n + 1) / 2
}

// Precondition: allow all n to match provided tests (including n = 0).
predicate precondition(n: nat)
{
  true
}

// Postcondition:
// 1) result.0 is exactly the Gauss sum (as an int).
// 2) result.1 is the average:
//    - if n = 0, it is 0.0 (per tests)
//    - if n > 0, it is real(result.0) / real(n)
// This fully determines the output for every n.
predicate postcondition(n: nat, result: (int, real))
{
  result.0 == gaussSumNat(n) &&
  (n == 0 ==> result.1 == 0.0) &&
  (n > 0 ==> result.1 == (result.0 as real) / (n as real))
}

method sumAndAverage(n: nat) returns (result: (int, real))
  requires precondition(n)
  ensures postcondition(n, result)
{
  var sumNat: nat := gaussSumNat(n);
  var sumInt: int := sumNat;

  if n == 0 {
    result := (sumInt, 0.0);
  } else {
    var avg: real := (sumInt as real) / (n as real);
    result := (sumInt, avg);
  }
}
