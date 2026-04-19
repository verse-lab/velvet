// Problem Description
//   isEven: determine whether a given integer is even
//   Natural language breakdown:
//   1. The input is an integer n.
//   2. The output is a Boolean.
//   3. The output is true exactly when n is even.
//   4. The output is false exactly when n is odd.
//   5. Evenness for integers can be characterized by remainder modulo 2 being 0.
//   6. There are no preconditions: the function is defined for all integers.

// Helper definition: evenness via Int modulo.
predicate IntIsEven(n: int)
{
  n % 2 == 0
}

method isEven(n: int) returns (result: bool)
  ensures result == true <==> IntIsEven(n)
{
  if n % 2 == 0 {
    result := true;
  } else {
    result := false;
  }
}
