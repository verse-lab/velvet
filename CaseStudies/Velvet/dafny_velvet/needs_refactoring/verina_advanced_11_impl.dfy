/* Problem Description
    findMajorityElement: Find the majority element in a list of integers
    Natural language breakdown:
    1. We are given a list of integers (may include duplicates and negative numbers)
    2. A majority element is defined as an element that appears strictly more than half the number of times in the list
    3. Formally, element x is a majority element if lst.count x > lst.length / 2
    4. If such a majority element exists, return that element
    5. If no majority element exists, return -1
    6. Edge case: Empty list has no majority element, return -1
    7. Note: There can be at most one majority element in any list (since it must appear more than half the time)
    8. The result is either the unique majority element or -1
*/

// Helper function to count occurrences of x in sequence lst
function count(lst: seq<int>, x: int): nat
  decreases |lst|
{
  if |lst| == 0 then 0
  else if lst[0] == x then 1 + count(lst[1..], x)
  else count(lst[1..], x)
}

// Lemma: count of concatenation
lemma CountConcat(s1: seq<int>, s2: seq<int>, x: int)
  ensures count(s1 + s2, x) == count(s1, x) + count(s2, x)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    assert (s1 + s2)[0] == s1[0];
    assert (s1 + s2)[1..] == s1[1..] + s2;
    CountConcat(s1[1..], s2, x);
  }
}

// Helper function to count occurrences of x in lst[0..j]
function countPrefix(lst: seq<int>, x: int, j: nat): nat
  requires j <= |lst|
  decreases j
{
  count(lst[..j], x)
}

// Helper predicate to check if an element is a majority element
ghost predicate isMajorityElement(lst: seq<int>, x: int)
{
  count(lst, x) > |lst| / 2
}

// Helper predicate to check if a majority element exists
ghost predicate hasMajorityElement(lst: seq<int>)
{
  exists x :: x in lst && isMajorityElement(lst, x)
}

// Precondition: no restrictions on input
ghost predicate precondition(lst: seq<int>)
{
  true
}

// Postcondition: result is either the majority element or -1
ghost predicate postcondition(lst: seq<int>, result: int)
{
  (hasMajorityElement(lst) ==> (result in lst && isMajorityElement(lst, result))) &&
  (!hasMajorityElement(lst) ==> result == -1)
}

// Lemma: If we've checked all elements and found none with count > threshold, no majority exists
lemma NoMajorityIfNoneFound(lst: seq<int>, i: nat)
  requires i <= |lst|
  requires forall k :: 0 <= k < i ==> !isMajorityElement(lst, lst[k])
  ensures i == |lst| ==> !hasMajorityElement(lst)
{
  if i == |lst| && hasMajorityElement(lst) {
    // There exists a majority element x
    var x :| x in lst && isMajorityElement(lst, x);
    // x must appear at some index
    var idx :| 0 <= idx < |lst| && lst[idx] == x;
    // We've checked all indices, so idx < i = |lst|
    assert !isMajorityElement(lst, lst[idx]);
    assert lst[idx] == x;
    assert isMajorityElement(lst, x);
    assert false;
  }
}

// Lemma: count in prefix increases by 1 when element matches
lemma CountPrefixIncrement(lst: seq<int>, x: int, j: nat)
  requires 0 <= j < |lst|
  requires lst[j] == x
  ensures countPrefix(lst, x, j + 1) == countPrefix(lst, x, j) + 1
{
  assert lst[..j+1] == lst[..j] + [lst[j]];
  CountConcat(lst[..j], [lst[j]], x);
  assert count([lst[j]], x) == 1;
}

// Lemma: count in prefix stays same when element doesn't match
lemma CountPrefixSame(lst: seq<int>, x: int, j: nat)
  requires 0 <= j < |lst|
  requires lst[j] != x
  ensures countPrefix(lst, x, j + 1) == countPrefix(lst, x, j)
{
  assert lst[..j+1] == lst[..j] + [lst[j]];
  CountConcat(lst[..j], [lst[j]], x);
  assert count([lst[j]], x) == 0;
}

// Lemma: full prefix equals the whole list
lemma CountPrefixFull(lst: seq<int>, x: int)
  ensures countPrefix(lst, x, |lst|) == count(lst, x)
{
  assert lst[..|lst|] == lst;
}

// Main method
method findMajorityElement(lst: seq<int>) returns (result: int)
  requires precondition(lst)
  ensures postcondition(lst, result)
{
  var n := |lst|;
  var threshold := n / 2;
  var i := 0;
  var found := false;
  var candidate: int := -1;

  while i < n
    // i is bounded by list length
    invariant 0 <= i <= n
    // found implies candidate is a majority element in the list
    invariant found == true ==> (candidate in lst && isMajorityElement(lst, candidate))
    // not found implies no majority element among first i elements
    invariant found == false ==> (forall k :: 0 <= k < i ==> !isMajorityElement(lst, lst[k]))
    decreases n - i
  {
    var elem := lst[i];
    var cnt := 0;
    var j := 0;

    // Count occurrences of elem in lst
    while j < n
      // j is bounded by list length
      invariant 0 <= j <= n
      // cnt equals occurrences of elem in lst[0..j]
      invariant cnt == countPrefix(lst, elem, j)
      // preserve outer loop invariants
      invariant found == true ==> (candidate in lst && isMajorityElement(lst, candidate))
      invariant 0 <= i < n
      invariant elem == lst[i]
      invariant found == false ==> (forall k :: 0 <= k < i ==> !isMajorityElement(lst, lst[k]))
      decreases n - j
    {
      if lst[j] == elem {
        CountPrefixIncrement(lst, elem, j);
        cnt := cnt + 1;
      } else {
        CountPrefixSame(lst, elem, j);
      }
      j := j + 1;
    }

    // After inner loop, cnt == count(lst, elem)
    CountPrefixFull(lst, elem);
    assert cnt == count(lst, elem);

    // Check if this element is a majority
    if cnt > threshold {
      found := true;
      candidate := elem;
      assert isMajorityElement(lst, elem);
    }

    i := i + 1;
  }

  if found {
    result := candidate;
  } else {
    NoMajorityIfNoneFound(lst, i);
    assert !hasMajorityElement(lst);
    result := -1;
  }
}