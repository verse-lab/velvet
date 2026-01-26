/* Problem Description
    hasOppositeSign: determine whether two integers have opposite signs.

    Natural language breakdown:
    1. The input consists of two integers a and b.
    2. Zero is considered neither positive nor negative.
    3. Two integers have opposite signs exactly when one is strictly positive
       and the other is strictly negative.
    4. Equivalently, both must be nonzero and their signs (via Int.sign)
       must be different and opposite.
    5. Int.sign x = 1 if x > 0; Int.sign x = -1 if x < 0; Int.sign x = 0 if x = 0.
    6. The method should return true iff a and b have opposite signs.
    7. It should return false if both are nonnegative, both are nonpositive,
       or if at least one is zero.

    We formalize this using inequalities on Int.
*/

// Specification
predicate hasOppositeSignSpec(a: int, b: int)
{
  (a > 0 && b < 0) || (a < 0 && b > 0)
}

// Implementation
method hasOppositeSign(a: int, b: int) returns (result: bool)
  ensures result == true <==> hasOppositeSignSpec(a, b)
{
  if a > 0 && b < 0 {
    result := true;
  } else if a < 0 && b > 0 {
    result := true;
  } else {
    result := false;
  }
}