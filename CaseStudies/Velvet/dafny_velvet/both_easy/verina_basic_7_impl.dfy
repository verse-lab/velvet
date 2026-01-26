/* Problem Description
    sumOfSquaresOfFirstNOddNumbers: Sum of squares of the first n odd natural numbers.
    Natural language breakdown:
    1. The input n is a natural number, so it is non-negative.
    2. The first n odd natural numbers are 1, 3, 5, ..., (2*n - 1).
    3. The desired output is the sum of the squares of these n odd numbers.
    4. The result must match the closed-form value (n * (2*n - 1) * (2*n + 1)) / 3.
    5. The function is total: it must accept any n : Nat.
*/

// Helper: the numerator of the closed-form expression.
// We keep this as a separate definition to improve readability.
function oddSquaresClosedFormNumerator(n: nat): nat
{
  n * (2 * n - 1) * (2 * n + 1)
}

// Precondition: none (the problem statement allows all Nat inputs).
predicate precondition(n: nat)
{
  true
}

// Postcondition:
// The result is the natural-number division by 3 of the closed-form numerator.
predicate postcondition(n: nat, result: nat)
{
  result == oddSquaresClosedFormNumerator(n) / 3
}

method sumOfSquaresOfFirstNOddNumbers(n: nat) returns (result: nat)
  requires precondition(n)
  ensures postcondition(n, result)
{
  var num := oddSquaresClosedFormNumerator(n);
  var res := num / 3;
  result := res;
}

