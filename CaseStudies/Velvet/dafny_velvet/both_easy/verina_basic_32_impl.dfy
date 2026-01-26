// Problem Description
//   swapFirstAndLast: swap the first and last elements of a non-empty array of integers.
//   Natural language breakdown:
//   1. Input is an array `a : Array Int`.
//   2. The input array is assumed to be non-empty (size > 0).
//   3. The output is a new array with the same size as the input.
//   4. The element at index 0 of the output equals the last element of the input (index a.size - 1).
//   5. The element at the last index of the output equals the first element of the input (index 0).
//   6. Every element at an index strictly between 0 and the last index is unchanged.
//   7. Special case: if the array has size 1, swapping first and last leaves the array unchanged.

// Helper: the last index of a non-empty array
function lastIdx(a: seq<int>): nat
  requires |a| > 0
{
  |a| - 1
}

predicate precondition(a: seq<int>)
{
  0 < |a|
}

predicate postcondition(a: seq<int>, result: seq<int>)
  requires |a| > 0
{
  |result| == |a| &&
  // pointwise characterization
  (forall i :: 0 <= i < |a| ==>
    (result[i] ==
      if i == 0 then a[lastIdx(a)]
      else if i == lastIdx(a) then a[0]
      else a[i]))
}

method swapFirstAndLast(a: seq<int>) returns (result: seq<int>)
  requires precondition(a)
  ensures postcondition(a, result)
{
  var n := |a|;
  var last := n - 1;

  // If size is 1, swapping first/last is identity; otherwise perform a swap.
  if n == 1 {
    result := a;
  } else {
    var firstVal := a[0];
    var lastVal := a[last];
    result := a[0 := lastVal][last := firstVal];
  }
}
