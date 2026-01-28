/* Problem Description
    myMin: Determine the minimum of two integers.
    Natural language breakdown:
    1. The input consists of two integers a and b.
    2. The output is an integer result.
    3. The result must be less than or equal to a, and less than or equal to b.
    4. The result must be one of the inputs (either a or b).
    5. When a = b, returning either one is allowed (they are equal).
*/

method myMin(a: int, b: int) returns (result: int)
  ensures result <= a
  ensures result <= b
  ensures result == a || result == b
{
  if a <= b {
    result := a;
  } else {
    result := b;
  }
}

