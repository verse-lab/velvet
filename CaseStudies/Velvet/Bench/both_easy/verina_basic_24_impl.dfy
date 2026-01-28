// Problem Description
//   verina_basic_24: difference between first even and first odd integers in an array.
//   Natural language breakdown:
//   1. Input is an array `a : Array Int`.
//   2. The array is assumed non-empty and contains at least one even element and at least one odd element.
//   3. "First even" means the element at the smallest index `i` such that `Even (a[i]!)`.
//   4. "First odd" means the element at the smallest index `j` such that `Odd (a[j]!)`.
//   5. The output is an integer equal to (first even element) minus (first odd element).
//   6. The result should be uniquely determined by the minimality of these indices.

// Helper: predicate that an index is the first index satisfying a property.
predicate IsFirstIdx(a: seq<int>, p: int -> bool, i: nat)
{
  i < |a| && p(a[i]) && (forall k :: 0 <= k < i ==> !p(a[k]))
}

// Preconditions: array must contain at least one even and at least one odd element.
predicate precondition(a: seq<int>)
{
  (exists i :: 0 <= i < |a| && a[i] % 2 == 0) &&
  (exists j :: 0 <= j < |a| && a[j] % 2 != 0)
}

// Postcondition: there exist minimal indices of first even and first odd,
// and result is their difference.
ghost predicate postcondition(a: seq<int>, result: int)
{
  exists i: nat, j: nat ::
    IsFirstIdx(a, x => x % 2 == 0, i) &&
    IsFirstIdx(a, x => x % 2 != 0, j) &&
    result == a[i] - a[j]
}

method firstEvenOddDifference(a: seq<int>) returns (result: int)
  requires precondition(a)
  ensures postcondition(a, result)
{
  var i: nat := 0;
  var foundEven: bool := false;
  var evenVal: int := 0;

  while i < |a| && !foundEven
    // Invariant: i is always within [0, a.size]; needed for safe access and for reasoning about termination.
    invariant i <= |a|
    // Invariant: all indices scanned so far (< i) are not even; this gives the minimality part for the first-even witness.
    invariant forall k :: 0 <= k < i ==> a[k] % 2 != 0
    // Invariant: once foundEven is true, current i points to an even element, evenVal matches it, and it's the first such index.
    invariant foundEven == true ==> (i < |a| && a[i] % 2 == 0 && evenVal == a[i] && (forall k :: 0 <= k < i ==> a[k] % 2 != 0))
    // Invariant: if we haven't found an even yet, there still exists an even at some index t >= i (from precondition).
    invariant foundEven == false ==> (exists t :: i <= t < |a| && a[t] % 2 == 0)
    // Invariant: if we reach/past the end, then we must have found an even.
    invariant |a| <= i ==> foundEven == true
    decreases |a| - i
  {
    if a[i] % 2 == 0 {
      evenVal := a[i];
      foundEven := true;
      break;
    }
    i := i + 1;
  }

  var j: nat := 0;
  var foundOdd: bool := false;
  var oddVal: int := 0;

  while j < |a| && !foundOdd
    // Invariant: j is always within [0, a.size]; needed for safe access and for reasoning about termination.
    invariant j <= |a|
    // Invariant: all indices scanned so far (< j) are not odd; this gives the minimality part for the first-odd witness.
    invariant forall k :: 0 <= k < j ==> a[k] % 2 == 0
    // Invariant: once foundOdd is true, current j points to an odd element, oddVal matches it, and it's the first such index.
    invariant foundOdd == true ==> (j < |a| && a[j] % 2 != 0 && oddVal == a[j] && (forall k :: 0 <= k < j ==> a[k] % 2 == 0))
    // Invariant: if we haven't found an odd yet, there still exists an odd at some index t >= j (from precondition).
    invariant foundOdd == false ==> (exists t :: j <= t < |a| && a[t] % 2 != 0)
    // Invariant: if we reach/past the end, then we must have found an odd.
    invariant |a| <= j ==> foundOdd == true
    decreases |a| - j
  {
    if a[j] % 2 != 0 {
      oddVal := a[j];
      foundOdd := true;
      break;
    }
    j := j + 1;
  }

  result := evenVal - oddVal;
}
