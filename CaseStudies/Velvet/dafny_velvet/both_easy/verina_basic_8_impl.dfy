/* Problem Description
    myMin: Determine the minimum of two integers.
    Natural language breakdown:
    1. The input consists of two integers a and b.
    2. The output is an integer result.
    3. The result must be less than or equal to a, and less than or equal to b.
    4. The result must be one of the inputs (either a or b).
    5. When a = b, returning either one is allowed (they are equal).
*/

// Precondition: no requirements
predicate precondition(a: int, b: int)
{
  true
}

// Postcondition: result is the minimum of a and b
predicate postcondition(a: int, b: int, result: int)
{
  result <= a && result <= b && (result == a || result == b)
}

method myMin(a: int, b: int) returns (result: int)
  requires precondition(a, b)
  ensures postcondition(a, b, result)
{
  if a <= b {
    result := a;
  } else {
    result := b;
  }
}

