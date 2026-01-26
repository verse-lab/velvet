/* Problem Description
    firstDuplicate: Find the first duplicate integer in a list when scanning left to right
    Natural language breakdown:
    1. We are given a list of integers
    2. We scan from left to right, looking for the first element that has appeared before
    3. "First duplicate" means the first position j where lst[j] equals some earlier lst[i] (i < j)
    4. We want to find the smallest index j such that lst[j] appears in lst[0..j-1]
    5. The result is the value at that index j
    6. If no such duplicate exists, return none (-1 in Dafny)
    7. Edge cases:
       - Empty list: no duplicates, return -1
       - Single element: no duplicates, return -1
       - All distinct elements: return -1
       - Multiple duplicates: return the one with earliest second occurrence
    8. Key insight: We're looking for the first index j where lst[0..j] contains lst[j]
*/

// Helper predicate to check if a value appears in a sequence
ghost predicate contains(lst: seq<int>, x: int)
{
  exists i :: 0 <= i < |lst| && lst[i] == x
}

// Helper function to check if a value appears in a sequence (for runtime)
method Contains(lst: seq<int>, x: int) returns (result: bool)
  ensures result == contains(lst, x)
{
  result := false;
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant result == contains(lst[..i], x)
    decreases |lst| - i
  {
    if lst[i] == x {
      result := true;
    }
    i := i + 1;
  }
}

// Precondition: no restrictions on input
ghost predicate precondition(lst: seq<int>)
{
  true
}

// Postcondition: Characterize the first duplicate
// When result >= 0:
//   - There exists an index j where lst[j] = result and result appears in lst[0..j-1]
//   - j is the smallest such index (no earlier index has this property)
// When result is -1:
//   - No element appears twice (no index j has lst[j] in its prefix)
ghost predicate postcondition(lst: seq<int>, result: int)
{
  if result == -1 then
    // No element appears in its prefix (no duplicates)
    forall j :: 0 <= j < |lst| ==> !contains(lst[..j], lst[j])
  else
    // There exists a position j where:
    // 1. lst[j] = result
    // 2. result appears in the prefix lst[0..j-1]
    // 3. j is minimal (no earlier position has an element appearing in its prefix)
    exists j :: 0 <= j < |lst| &&
                lst[j] == result &&
                contains(lst[..j], result) &&
                (forall k :: 0 <= k < j ==> !contains(lst[..k], lst[k]))
}

// Main method

method firstDuplicate(lst: seq<int>) returns (result: int)
  decreases *
  requires precondition(lst)
  ensures postcondition(lst, result)
{
  var i := 0;
  var found := -1;  // Using -1 instead of Option type

  while i < |lst| && found == -1
    // Invariant 1: Index bounds
    invariant 0 <= i <= |lst|
    // Invariant 2: No duplicates found yet
    invariant found == -1 ==> (forall k :: 0 <= k < i ==> !contains(lst[..k], lst[k]))
    // Invariant 3: If found != -1, it's the first duplicate
    invariant found != -1 ==>
      (exists j :: 0 <= j < |lst| && j <= i && lst[j] == found && contains(lst[..j], found) &&
        (forall k :: 0 <= k < j ==> !contains(lst[..k], lst[k])))
    // Invariant 4: normalExit tracks whether we found a duplicate
    decreases *
  {
    var current := lst[i];
    var prefixList := lst[..i];

    // Use the Contains method to check if current is in prefixList
    var containsCurrent := Contains(prefixList, current);

    if containsCurrent {
      found := current;
      assert lst[i] == found;
      assert contains(lst[..i], found);
      assert forall k :: 0 <= k < i ==> !contains(lst[..k], lst[k]);
    } else {
      i := i + 1;
    }
  }

  // Establish postcondition
  if found == -1 {
    // If found == -1, we never executed break (break only happens when setting found)
    // So the loop exited because the loop guard became false
    // Loop guard: i < |lst| && found == -1
    // Since found == -1 is true, we must have i >= |lst|

    assert i <= |lst|;  // From invariant 1

    // The tricky part: we exited normally, so the loop condition was false
    // But we can't directly assert this with break statements
    // Instead, reason that if found == -1, we only increment i and never break
    // So we must have reached i == |lst|

    assert i == |lst|;

    // From invariant 2 with i == |lst|
    assert forall k :: 0 <= k < |lst| ==> !contains(lst[..k], lst[k]);

    // This matches the postcondition for found == -1
  } else {
    // found != -1, from invariant 3 we have the witness
    assert exists j :: 0 <= j < |lst| && j <= i && lst[j] == found && contains(lst[..j], found) &&
      (forall k :: 0 <= k < j ==> !contains(lst[..k], lst[k]));

    // This matches the postcondition for found != -1
  }

  result := found;
}