// Problem Description
// mergeSorted: Merge two sorted arrays of natural numbers into a single sorted array
// **IMPORTANT: complexity should be O(n)**
// Natural language breakdown:
// 1. We have two input arrays a1 and a2, both containing natural numbers
// 2. Both input arrays must be sorted in non-decreasing order (precondition)
// 3. The output array must contain all elements from both input arrays
// 4. Each element appears exactly as many times as it appears in a1 plus a2 combined
// 5. The output array must also be sorted in non-decreasing order
// 6. The size of the output equals the sum of sizes of the two input arrays
// 7. This is a merge operation that preserves all elements (including duplicates)

// Helper: check if a sequence is sorted in non-decreasing order
ghost predicate isSortedArray(arr: seq<nat>)
{
  forall i, j :: 0 <= i < j < |arr| ==> arr[i] <= arr[j]
}

// Helper: count occurrences of a value in a sequence
function countInArray(arr: seq<nat>, v: nat): nat
{
  if |arr| == 0 then 0
  else if arr[0] == v then 1 + countInArray(arr[1..], v)
  else countInArray(arr[1..], v)
}

// Lemma: count in concatenation equals sum of counts
lemma CountConcat(s1: seq<nat>, s2: seq<nat>, v: nat)
  ensures countInArray(s1 + s2, v) == countInArray(s1, v) + countInArray(s2, v)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    assert (s1 + s2)[0] == s1[0];
    assert (s1 + s2)[1..] == s1[1..] + s2;
    CountConcat(s1[1..], s2, v);
  }
}

// Lemma: appending an element
lemma CountAppend(s: seq<nat>, x: nat, v: nat)
  ensures countInArray(s + [x], v) == countInArray(s, v) + (if x == v then 1 else 0)
{
  CountConcat(s, [x], v);
  assert countInArray([x], v) == (if x == v then 1 else 0);
}

// Lemma: taking i+1 elements is same as taking i elements plus the i-th element
lemma TakeSucc(s: seq<nat>, i: nat)
  requires i < |s|
  ensures s[..i+1] == s[..i] + [s[i]]
{
  // This is automatic in Dafny
}

// Lemma: count preservation when taking from a1
lemma CountInvariantMaintainedA1(a1: seq<nat>, a2: seq<nat>, result: seq<nat>, i: nat, j: nat, v: nat)
  requires i < |a1|
  requires j <= |a2|
  requires countInArray(result, v) == countInArray(a1[..i], v) + countInArray(a2[..j], v)
  ensures countInArray(result + [a1[i]], v) == countInArray(a1[..i+1], v) + countInArray(a2[..j], v)
{
  CountAppend(result, a1[i], v);
  TakeSucc(a1, i);
  CountConcat(a1[..i], [a1[i]], v);
}

// Lemma: count preservation when taking from a2
lemma CountInvariantMaintainedA2(a1: seq<nat>, a2: seq<nat>, result: seq<nat>, i: nat, j: nat, v: nat)
  requires i <= |a1|
  requires j < |a2|
  requires countInArray(result, v) == countInArray(a1[..i], v) + countInArray(a2[..j], v)
  ensures countInArray(result + [a2[j]], v) == countInArray(a1[..i], v) + countInArray(a2[..j+1], v)
{
  CountAppend(result, a2[j], v);
  TakeSucc(a2, j);
  CountConcat(a2[..j], [a2[j]], v);
}

// Precondition: both input arrays must be sorted
ghost predicate precondition(a1: seq<nat>, a2: seq<nat>)
{
  isSortedArray(a1) && isSortedArray(a2)
}

// Postcondition clauses
// 1. The result size equals the sum of input sizes
ghost predicate ensures1(a1: seq<nat>, a2: seq<nat>, result: seq<nat>)
{
  |result| == |a1| + |a2|
}

// 2. The result is sorted in non-decreasing order
ghost predicate ensures2(a1: seq<nat>, a2: seq<nat>, result: seq<nat>)
{
  isSortedArray(result)
}

// 3. Every element's count in result equals its count in a1 plus its count in a2
ghost predicate ensures3(a1: seq<nat>, a2: seq<nat>, result: seq<nat>)
{
  forall v :: countInArray(result, v) == countInArray(a1, v) + countInArray(a2, v)
}

ghost predicate postcondition(a1: seq<nat>, a2: seq<nat>, result: seq<nat>)
{
  ensures1(a1, a2, result) &&
  ensures2(a1, a2, result) &&
  ensures3(a1, a2, result)
}

method mergeSorted(a1: seq<nat>, a2: seq<nat>) returns (result: seq<nat>)
  requires precondition(a1, a2)
  ensures postcondition(a1, a2, result)
{
  result := [];
  var i := 0;
  var j := 0;

  while i < |a1| || j < |a2|
    // Invariant 1: Index bounds
    invariant i <= |a1|
    invariant j <= |a2|
    // Invariant 2: Result size tracks progress
    invariant |result| == i + j
    // Invariant 3: Result array is sorted
    invariant isSortedArray(result)
    // Invariant 4: Count preservation for elements processed so far
    invariant forall v :: countInArray(result, v) == countInArray(a1[..i], v) + countInArray(a2[..j], v)
    // Invariant 5: Last element of result is <= remaining elements in a1
    invariant |result| > 0 && i < |a1| ==> result[|result| - 1] <= a1[i]
    // Invariant 6: Last element of result is <= remaining elements in a2
    invariant |result| > 0 && j < |a2| ==> result[|result| - 1] <= a2[j]
    decreases |a1| + |a2| - i - j
  {
    ghost var oldResult := result;
    ghost var oldI := i;
    ghost var oldJ := j;

    if i >= |a1| {
      // a1 exhausted, take from a2
      result := result + [a2[j]];

      // Help verify count invariant
      forall v
        ensures countInArray(result, v) == countInArray(a1[..i], v) + countInArray(a2[..j+1], v)
      {
        CountInvariantMaintainedA2(a1, a2, oldResult, oldI, oldJ, v);
      }

      j := j + 1;
    } else if j >= |a2| {
      // a2 exhausted, take from a1
      result := result + [a1[i]];

      // Help verify count invariant
      forall v
        ensures countInArray(result, v) == countInArray(a1[..i+1], v) + countInArray(a2[..j], v)
      {
        CountInvariantMaintainedA1(a1, a2, oldResult, oldI, oldJ, v);
      }

      i := i + 1;
    } else {
      // Both have elements, take smaller
      if a1[i] <= a2[j] {
        result := result + [a1[i]];

        // Help verify count invariant
        forall v
          ensures countInArray(result, v) == countInArray(a1[..i+1], v) + countInArray(a2[..j], v)
        {
          CountInvariantMaintainedA1(a1, a2, oldResult, oldI, oldJ, v);
        }

        i := i + 1;
      } else {
        result := result + [a2[j]];

        // Help verify count invariant
        forall v
          ensures countInArray(result, v) == countInArray(a1[..i], v) + countInArray(a2[..j+1], v)
        {
          CountInvariantMaintainedA2(a1, a2, oldResult, oldI, oldJ, v);
        }

        j := j + 1;
      }
    }
  }

  // After loop: i == |a1| && j == |a2|
  assert i == |a1| && j == |a2|;

  // From invariant 2: |result| == i + j == |a1| + |a2|
  assert |result| == |a1| + |a2|;

  // From invariant 3: result is sorted
  assert isSortedArray(result);

  // From invariant 4 with i == |a1| and j == |a2|:
  assert a1[..i] == a1;
  assert a2[..j] == a2;
  assert forall v :: countInArray(result, v) == countInArray(a1, v) + countInArray(a2, v);
}