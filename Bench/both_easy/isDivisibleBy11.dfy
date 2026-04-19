/* Problem Description
    isDivisibleBy11: Determine whether a given integer is divisible by 11
    Natural language breakdown:
    1. We have an input integer n
    2. An integer n is divisible by 11 if and only if there exists an integer k such that n = 11 * k
    3. Equivalently, n is divisible by 11 if and only if n % 11 = 0
    4. The method should return true if n is divisible by 11
    5. The method should return false if n is not divisible by 11
    6. Zero is divisible by 11 (0 = 11 * 0)
    7. Negative integers can also be divisible by 11 (e.g., -11, -22)
    8. The divisibility relation is symmetric under negation

    Property-oriented specification:
    - We use the built-in divisibility predicate from Lean: 11 | n
    - This means: there exists an integer c such that n = 11 * c
    - The result should be true if and only if 11 divides n
*/

method isDivisibleBy11(n: int) returns (result: bool)
  ensures result == true <==> n % 11 == 0
{
  var remainder := n % 11;
  if remainder == 0 {
    result := true;
  } else {
    result := false;
  }
}

