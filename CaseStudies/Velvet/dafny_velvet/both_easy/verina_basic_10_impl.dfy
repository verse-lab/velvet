/* Problem Description
    isGreater: determine if an integer is strictly greater than every element in an array
    Natural language breakdown:
    1. Inputs are an integer n and an array a of integers.
    2. The method returns a Boolean.
    3. The result is true exactly when n is strictly greater than every element in a.
    4. The result is false when there exists at least one element x in a with x ≥ n.
    5. Empty arrays are rejected (see reject input).
*/

// Precondition: reject empty arrays
predicate precondition(n: int, a: seq<int>)
{
  |a| > 0
}

// Postcondition: Boolean meaning of being strictly greater than every element
predicate postcondition(n: int, a: seq<int>, result: bool)
{
  result == true <==> (forall i :: 0 <= i < |a| ==> a[i] < n)
}

method isGreater(n: int, a: seq<int>) returns (result: bool)
  requires precondition(n, a)
  ensures postcondition(n, a, result)
{
  var ok := true;
  var i: nat := 0;

  while i < |a|
    // Invariant: i stays within bounds
    invariant 0 <= i <= |a|
    // Invariant: ok is true iff all elements seen so far are < n
    invariant ok == true <==> (forall j :: 0 <= j < i ==> a[j] < n)
  {
    if a[i] < n {
      // ok remains true
    } else {
      ok := false;
    }
    i := i + 1;
  }

  result := ok;
}

