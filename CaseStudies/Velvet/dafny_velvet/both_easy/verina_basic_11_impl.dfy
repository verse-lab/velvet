/* Problem Description
    lastDigit: extract the last decimal digit of a non-negative integer.
    Natural language breakdown:
    1. Input n is a natural number (hence non-negative by type).
    2. The last digit in base 10 is the remainder when dividing n by 10.
    3. The result must be a natural number between 0 and 9 inclusive.
    4. The returned digit must satisfy: result = n % 10.
*/

// Precondition: no additional requirements because n is already non-negative
predicate precondition(n: nat)
{
  true
}

// Postcondition: result is exactly the remainder mod 10 and is a decimal digit
predicate postcondition(n: nat, result: nat)
{
  result == n % 10 && result < 10
}

method lastDigit(n: nat) returns (result: nat)
  requires precondition(n)
  ensures postcondition(n, result)
{
  var d := n % 10;
  result := d;
}

