/* Problem Description
    verina_basic_6: Minimum of three integers

    Natural language breakdown:
    1. The input consists of three integers a, b, and c.
    2. The function returns an integer result intended to be the minimum among a, b, and c.
    3. The result must be less than or equal to each input: result ≤ a, result ≤ b, and result ≤ c.
    4. The result must be one of the inputs: result = a or result = b or result = c.
    5. There are no rejected inputs; all Int inputs are valid.
*/

// Precondition: no rejected inputs
predicate precondition(a: int, b: int, c: int)
{
  true
}

// Postcondition: result is the minimum of the three inputs
predicate postcondition(a: int, b: int, c: int, result: int)
{
  (result <= a && result <= b && result <= c) &&
  (result == a || result == b || result == c)
}

method minOfThree(a: int, b: int, c: int) returns (result: int)
  requires precondition(a, b, c)
  ensures postcondition(a, b, c, result)
{
  var m := a;
  if b <= m {
    m := b;
  }
  if c <= m {
    m := c;
  }
  result := m;
}

