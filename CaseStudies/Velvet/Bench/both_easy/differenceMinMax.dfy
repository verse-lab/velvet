// Problem Description
//   differenceMinMax: compute the difference between the maximum and minimum values of a nonempty array of Int.
//   Natural language breakdown:
//   1. The input is an array `a : Array Int`.
//   2. The input array is assumed to be non-empty.
//   3. Let `mn` be the minimum value occurring in `a` and `mx` be the maximum value occurring in `a`.
//   4. The returned integer is `mx - mn`.
//   5. The result must be 0 when all elements are equal or when the array has exactly one element.
//   6. The specification should describe `mn` and `mx` as bounds achieved by some array elements.

// Helper predicate: value occurs in array
predicate InArray(a: seq<int>, v: int)
{
  exists i :: 0 <= i < |a| && a[i] == v
}

// Helper predicate: `mn` is a minimum value achieved in the array
predicate IsMinOfArray(a: seq<int>, mn: int)
{
  InArray(a, mn) && (forall i :: 0 <= i < |a| ==> mn <= a[i])
}

// Helper predicate: `mx` is a maximum value achieved in the array
predicate IsMaxOfArray(a: seq<int>, mx: int)
{
  InArray(a, mx) && (forall i :: 0 <= i < |a| ==> a[i] <= mx)
}

method differenceMinMax(a: seq<int>) returns (result: int)
  requires |a| != 0
  ensures exists mn: int, mx: int ::
            IsMinOfArray(a, mn) &&
            IsMaxOfArray(a, mx) &&
            result == mx - mn
{
  var mn := a[0];
  var mx := a[0];

  var i: nat := 1;
  while i < |a|
    // Invariant: index stays within bounds (initially i=1; preserved by i := i+1; needed to justify accesses and to cover all elements on exit)
    invariant 1 <= i <= |a|
    // Invariant: mn is a minimum among the elements seen so far (0..i-1), and is achieved in that prefix
    // Initialization: mn=a[0] witnessed by j=0; Preservation: updating mn to v maintains min property; Sufficient with i=|a| to get global min.
    invariant (exists j :: 0 <= j < i && a[j] == mn) && (forall j :: 0 <= j < i ==> mn <= a[j])
    // Invariant: mx is a maximum among the elements seen so far (0..i-1), and is achieved in that prefix
    // Initialization: mx=a[0] witnessed by j=0; Preservation: updating mx to v maintains max property; Sufficient with i=|a| to get global max.
    invariant (exists j :: 0 <= j < i && a[j] == mx) && (forall j :: 0 <= j < i ==> a[j] <= mx)
  {
    var v := a[i];
    if v < mn {
      mn := v;
    }
    if v > mx {
      mx := v;
    }
    i := i + 1;
  }

  // This means mn is the global minimum and mx is the global maximum
  assert IsMinOfArray(a, mn);
  assert IsMaxOfArray(a, mx);

  result := mx - mn;
}
