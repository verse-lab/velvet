/* Problem Description
    hasCommonElement: Check whether two arrays of integers share any common element.
    Natural language breakdown:
    1. Inputs are two arrays `a` and `b` containing integers.
    2. The result is a boolean.
    3. The result is true exactly when there exists at least one integer value `x`
       that is an element of `a` and also an element of `b`.
    4. The result is false exactly when there is no integer value present in both arrays.
    5. Reject inputs: both arrays empty are considered invalid for this task.
*/

// Precondition: both arrays cannot be empty simultaneously
predicate precondition(a: seq<int>, b: seq<int>)
{
  !(|a| == 0 && |b| == 0)
}

// Postcondition: result matches existence of a common element
predicate postcondition(a: seq<int>, b: seq<int>, result: bool)
{
  result == true <==> (exists x :: x in a && x in b)
}

method hasCommonElement(a: seq<int>, b: seq<int>) returns (result: bool)
  requires precondition(a, b)
  ensures postcondition(a, b, result)
{
  var found := false;
  var i: nat := 0;

  while i < |a| && found == false
    invariant 0 <= i <= |a|
    invariant found == false ==> forall p :: 0 <= p < i ==> forall q :: 0 <= q < |b| ==> a[p] != b[q]
    invariant found == true ==> exists p :: 0 <= p < |a| && exists q :: 0 <= q < |b| && a[p] == b[q]
  {
    var j: nat := 0;
    while j < |b| && found == false
      invariant 0 <= j <= |b|
      invariant i < |a|
      invariant found == false ==> forall q :: 0 <= q < j ==> a[i] != b[q]
      invariant found == true ==> exists p :: 0 <= p < |a| && exists q :: 0 <= q < |b| && a[p] == b[q]
      invariant found == false ==> forall p :: 0 <= p < i ==> forall q :: 0 <= q < |b| ==> a[p] != b[q]
    {
      if a[i] == b[j] {
        found := true;
        assert a[i] == b[j];
        assert exists p :: 0 <= p < |a| && exists q :: 0 <= q < |b| && a[p] == b[q] by {
          assert 0 <= i < |a| && 0 <= j < |b| && a[i] == b[j];
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }

  // At loop exit, either found == true or we've checked everything
  if found {
    assert exists p :: 0 <= p < |a| && exists q :: 0 <= q < |b| && a[p] == b[q];
    assert exists x :: x in a && x in b by {
      var p :| 0 <= p < |a| && exists q :: 0 <= q < |b| && a[p] == b[q];
      var q :| 0 <= q < |b| && a[p] == b[q];
      assert a[p] in a && a[p] in b;
    }
  } else {
    assert i == |a|;
    assert forall p :: 0 <= p < |a| ==> forall q :: 0 <= q < |b| ==> a[p] != b[q];
    assert !(exists x :: x in a && x in b) by {
      if exists x :: x in a && x in b {
        var x :| x in a && x in b;
        var p :| 0 <= p < |a| && a[p] == x;
        var q :| 0 <= q < |b| && b[q] == x;
        assert a[p] == b[q];
        assert false;
      }
    }
  }

  result := found;
}

