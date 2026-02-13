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

ghost predicate isSorted(arr: seq<nat>)
{
  forall i, j :: 0 <= i < j < |arr| ==> arr[i] <= arr[j]
}

lemma isSorted_le(arr: seq<nat>, i: nat)
  requires isSorted(arr)
  requires i + 1 < |arr|
  ensures arr[i] <= arr[i + 1]
{
}

function count(arr: seq<nat>, v: nat): nat
{
  if |arr| == 0 then 0
  else if arr[0] == v then 1 + count(arr[1..], v)
  else count(arr[1..], v)
}

// Helper: count in concatenation equals sum of counts
lemma count_concat(s1: seq<nat>, s2: seq<nat>, v: nat)
  ensures count(s1 + s2, v) == count(s1, v) + count(s2, v)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    assert (s1 + s2)[0] == s1[0];
    assert (s1 + s2)[1..] == s1[1..] + s2;
    count_concat(s1[1..], s2, v);
  }
}

// Analogous to Lean's count_take theorem
lemma count_take(xs: seq<nat>, n: nat, a: nat)
  requires n < |xs|
  ensures count(xs[..n+1], a) == (if xs[n] == a then count(xs[..n], a) + 1 else count(xs[..n], a))
{
  assert xs[..n+1] == xs[..n] + [xs[n]];
  count_concat(xs[..n], [xs[n]], a);
}

method mergeSorted(a1: seq<nat>, a2: seq<nat>) returns (result: seq<nat>)
  requires isSorted(a1)
  requires isSorted(a2)
  ensures |result| == |a1| + |a2|
  ensures isSorted(result)
  ensures forall v :: count(result, v) == count(a1, v) + count(a2, v)
{
  result := [];
  var i := 0;
  var j := 0;

  while i < |a1| || j < |a2|
    invariant i <= |a1|
    invariant j <= |a2|
    invariant |result| == i + j
    invariant isSorted(result)
    invariant forall v :: count(result, v) == count(a1[..i], v) + count(a2[..j], v)
    invariant |result| > 0 && i < |a1| ==> result[|result| - 1] <= a1[i]
    invariant |result| > 0 && j < |a2| ==> result[|result| - 1] <= a2[j]
    decreases |a1| + |a2| - i - j
  {
    ghost var oldResult := result;

    if i >= |a1| {
      // a1 exhausted, take from a2
      result := result + [a2[j]];
      forall v
        ensures count(result, v) == count(a1[..i], v) + count(a2[..j+1], v)
      {
        count_concat(oldResult, [a2[j]], v);
        count_take(a2, j, v);
      }
      j := j + 1;
    } else if j >= |a2| {
      // a2 exhausted, take from a1
      result := result + [a1[i]];
      forall v
        ensures count(result, v) == count(a1[..i+1], v) + count(a2[..j], v)
      {
        count_concat(oldResult, [a1[i]], v);
        count_take(a1, i, v);
      }
      i := i + 1;
    } else {
      // Both have elements, take smaller
      if a1[i] <= a2[j] {
        result := result + [a1[i]];
        forall v
          ensures count(result, v) == count(a1[..i+1], v) + count(a2[..j], v)
        {
          count_concat(oldResult, [a1[i]], v);
          count_take(a1, i, v);
        }
        i := i + 1;
      } else {
        result := result + [a2[j]];
        forall v
          ensures count(result, v) == count(a1[..i], v) + count(a2[..j+1], v)
        {
          count_concat(oldResult, [a2[j]], v);
          count_take(a2, j, v);
        }
        j := j + 1;
      }
    }
  }

  assert a1[..i] == a1;
  assert a2[..j] == a2;
}
