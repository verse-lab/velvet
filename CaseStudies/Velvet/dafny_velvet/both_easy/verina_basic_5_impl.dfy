/*
Problem Description:
  multiply: Multiply two integers.
  Natural language breakdown:
  1. The input consists of two integers a and b.
  2. The output is an integer representing the arithmetic product of a and b.
  3. There are no restrictions on inputs (they may be negative, zero, or positive).
  4. The result is uniquely determined by integer multiplication.
*/

// Precondition: no requirements
predicate precondition(a: int, b: int)
{
  true
}

// Postcondition: result is the product of a and b
predicate postcondition(a: int, b: int, result: int)
{
  result == a * b
}

method multiply(a: int, b: int) returns (result: int)
  requires precondition(a, b)
  ensures postcondition(a, b, result)
{
  var prod := a * b;
  result := prod;
}

