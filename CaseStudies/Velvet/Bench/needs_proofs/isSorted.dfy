/* Problem Description
    isSorted: check whether an array of integers is sorted in non-decreasing order.
    Natural language breakdown:
    1. Input is an array of integers `a`; it may be empty or any length.
    2. The result is a boolean.
    3. The result is true exactly when every adjacent pair is ordered: for each index i with i+1 in bounds,
       we have a[i] ≤ a[i+1].
    4. When the result is true, the array is globally non-decreasing: for any indices i < j within bounds,
       a[i] ≤ a[j].
    5. When the result is false, the array is not adjacent-sorted, meaning there exists some adjacent inversion.
*/

// Adjacent non-decreasing order
predicate AdjacentSorted(a: seq<int>)
{
  forall i :: 0 <= i < |a| - 1 ==> a[i] <= a[i + 1]
}

// Global non-decreasing order
predicate GloballySorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// Helper lemma: if adjacent-sorted then globally-sorted
lemma AdjacentImpliesGlobal(a: seq<int>)
  requires AdjacentSorted(a)
  ensures GloballySorted(a)
{
  if |a| <= 1 {
    return;
  }

  forall i, j | 0 <= i < j < |a|
    ensures a[i] <= a[j]
  {
    if j == i + 1 {
      assert a[i] <= a[j];
    } else {
      var k := i;
      while k < j
        invariant i <= k <= j
        invariant a[i] <= a[k]
      {
        assert a[k] <= a[k + 1];
        k := k + 1;
      }
    }
  }
}

method isSorted(a: seq<int>) returns (result: bool)
  ensures result == true <==> GloballySorted(a)
{
  var sorted := true;
  var i: nat := 0;

  // Scan adjacent pairs; if we find an inversion, mark as unsorted and stop
  while i + 1 < |a| && sorted
    // Invariant: i stays within array bounds; always true for Nat index and needed for safe reads when loop cond holds
    // Init: i=0. Preserved: i increments. Sufficient: helps show indices mentioned in other invariants are in-range
    invariant i <= |a|
    // Invariant: if still marked sorted, all already-checked adjacent pairs (with index < i) are ordered
    // Init: i=0, vacuous. Preserved: when a[i] <= a[i+1], incrementing i makes the new checked pair become part of the prefix
    invariant sorted == true ==> (forall k :: 0 <= k < i && k + 1 < |a| ==> a[k] <= a[k + 1])
    // Invariant: if sorted=false, we have witnessed an inversion at some index k that is within the already-scanned range (k <= i)
    // Init: sorted=true so vacuous. Preserved: when we set sorted:=false at index i, we can witness k=i
    invariant sorted == false ==> (exists k :: 0 <= k <= i && k + 1 < |a| && a[k] > a[k + 1])
  {
    if a[i] > a[i + 1] {
      sorted := false;
    }
    i := i + 1;
  }

  // Prove postcondition
  if sorted {
    AdjacentImpliesGlobal(a);
  }

  result := sorted;
}

