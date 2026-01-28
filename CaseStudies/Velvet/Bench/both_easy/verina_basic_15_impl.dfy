/* Problem Description
    containsConsecutiveNumbers: determine whether an array of integers contains at least one pair of consecutive numbers
    Natural language breakdown:
    1. Input is an array `a` of integers; it may be empty or non-empty.
    2. A "consecutive pair" means there exists an index `i` such that `i + 1 < a.size` and `a[i] + 1 = a[i+1]`.
    3. The result is `true` iff such an index exists.
    4. If the array has size 0 or 1, then no such index exists and the result is `false`.
    5. There are no preconditions.
*/

// Helper predicate: there exists an adjacent index with successor-by-1 relation
predicate HasConsecutivePair(a: seq<int>)
{
  exists i :: 0 <= i < |a| - 1 && a[i] + 1 == a[i + 1]
}

method containsConsecutiveNumbers(a: seq<int>) returns (result: bool)
  ensures result == HasConsecutivePair(a)
{
  if |a| < 2 {
    result := false;
  } else {
    var i: nat := 0;
    var found := false;

    while i + 1 < |a| && !found
      invariant 0 <= i < |a|
      invariant !found ==> forall j :: 0 <= j < i ==> a[j] + 1 != a[j + 1]
      invariant found ==> exists j :: 0 <= j < |a| - 1 && a[j] + 1 == a[j + 1]
      decreases if found then 0 else |a| - i
    {
      if a[i] + 1 == a[i + 1] {
        found := true;
      } else {
        i := i + 1;
      }
    }

    result := found;
  }
}

