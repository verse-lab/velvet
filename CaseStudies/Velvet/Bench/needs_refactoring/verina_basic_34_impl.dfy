// Problem Description
//   findEvenNumbers: Extract even numbers from an array of integers, preserving order.
//   Natural language breakdown:
//   1. Input is an array of integers `arr` (may be empty).
//   2. Output is an array `result` containing only elements of `arr` that are even.
//   3. Every element of `result` is even.
//   4. Every even element occurring in `arr` appears in `result` with the same multiplicity.
//   5. The relative order of the kept (even) elements is the same as in `arr`.
//   6. There are no preconditions.

// Helper predicate: integer evenness.
function isEvenInt(x: int): bool
{
  x % 2 == 0
}

predicate precondition(arr: seq<int>)
{
  true
}

// Helper: count occurrences of x in sequence
function count(s: seq<int>, x: int): nat
{
  if |s| == 0 then 0
  else (if s[0] == x then 1 else 0) + count(s[1..], x)
}

// Lemma: count in empty sequence is 0
lemma CountEmpty(x: int)
  ensures count([], x) == 0
{
}

// Lemma: count in empty prefix is 0
lemma CountEmptyPrefix(s: seq<int>, x: int)
  ensures count(s[..0], x) == 0
{
  assert s[..0] == [];
}

// Lemma: count is preserved when appending an element
lemma CountAppend(s: seq<int>, x: int, y: int)
  ensures count(s + [y], x) == count(s, x) + (if y == x then 1 else 0)
{
  if |s| == 0 {
  } else {
    assert (s + [y])[1..] == s[1..] + [y];
  }
}

// Lemma: extending prefix by one element
lemma CountPrefixExtend(s: seq<int>, x: int, i: nat)
  requires i < |s|
  ensures count(s[..i+1], x) == count(s[..i], x) + (if s[i] == x then 1 else 0)
{
  var prefix := s[..i];
  var extended := s[..i+1];
  assert extended == prefix + [s[i]];
  CountAppend(prefix, x, s[i]);
}

// Helper: check if result is a subsequence of arr (preserving order)
ghost predicate IsSubsequence(result: seq<int>, arr: seq<int>)
{
  exists indices: seq<nat> ::
    |indices| == |result| &&
    (forall i :: 0 <= i < |indices| ==> indices[i] < |arr|) &&
    (forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]) &&
    (forall i :: 0 <= i < |indices| ==> result[i] == arr[indices[i]])
}

ghost predicate postcondition(arr: seq<int>, result: seq<int>)
{
  // Order preservation: result is a subsequence of arr
  IsSubsequence(result, arr) &&
  // Only evens are present.
  (forall x :: x in result ==> isEvenInt(x)) &&
  // Exact multiplicity of evens; no odds are included.
  (forall x ::
    (isEvenInt(x) ==> count(result, x) == count(arr, x)) &&
    (!isEvenInt(x) ==> count(result, x) == 0))
}

method findEvenNumbers(arr: seq<int>) returns (result: seq<int>)
  requires precondition(arr)
  ensures postcondition(arr, result)
{
  result := [];
  var indices: seq<nat> := [];
  var i: nat := 0;

  // Establish initial invariants
  assert forall j :: 0 <= j < |result| ==> isEvenInt(result[j]);
  forall x | !isEvenInt(x)
    ensures count(result, x) == 0
  {
    CountEmpty(x);
  }
  forall x | isEvenInt(x)
    ensures count(result, x) == count(arr[..i], x)
  {
    CountEmpty(x);
    CountEmptyPrefix(arr, x);
  }

  while i < |arr|
    // Loop index stays within bounds
    invariant i <= |arr|
    // result contains only even integers
    invariant forall j :: 0 <= j < |result| ==> isEvenInt(result[j])
    // For any odd value, its multiplicity in result is 0
    invariant forall x :: !isEvenInt(x) ==> count(result, x) == 0
    // For any even value, multiplicity in result equals multiplicity in the processed prefix
    invariant forall x :: isEvenInt(x) ==> count(result, x) == count(arr[..i], x)
    // Subsequence property: indices track where result elements come from
    invariant |indices| == |result|
    invariant forall k :: 0 <= k < |indices| ==> indices[k] < i
    invariant forall k :: 0 <= k < |indices| ==> indices[k] < |arr|
    invariant forall k :: 0 <= k < |indices| ==> result[k] == arr[indices[k]]
    invariant forall k, j :: 0 <= k < j < |indices| ==> indices[k] < indices[j]
  {
    ghost var oldResult := result;
    ghost var oldI := i;

    var x := arr[i];
    if isEvenInt(x) {
      result := result + [x];
      indices := indices + [i];

      // Prove invariants are maintained
      forall y | isEvenInt(y)
        ensures count(result, y) == count(arr[..i+1], y)
      {
        CountAppend(oldResult, y, x);
        CountPrefixExtend(arr, y, oldI);
      }

      forall y | !isEvenInt(y)
        ensures count(result, y) == 0
      {
        CountAppend(oldResult, y, x);
        assert !isEvenInt(x) ==> x != y;
      }
    } else {
      // x is odd, so we skip it
      forall y | isEvenInt(y)
        ensures count(result, y) == count(arr[..i+1], y)
      {
        CountPrefixExtend(arr, y, oldI);
      }
    }

    i := i + 1;
  }

  assert i == |arr|;
  assert arr[..i] == arr;

}
