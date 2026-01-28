// Problem Description
//   elementWiseModulo: compute the element-wise modulo (remainder) between two arrays of integers.
//   Natural language breakdown:
//   1. Inputs are two arrays a and b of integers.
//   2. The two arrays must have the same length.
//   3. Every element of b must be non-zero so that the modulo operation is defined.
//   4. The output is a new array result of integers.
//   5. The output has the same length as the input arrays.
//   6. For each valid index i, the output element result[i] equals a[i] % b[i].

// Helper predicate: all entries of an Int array are non-zero.
predicate allNonzero(b: seq<int>)
{
  forall i :: 0 <= i < |b| ==> b[i] != 0
}

method elementWiseModulo(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires |a| == |b|
  requires allNonzero(b)
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> result[i] == a[i] % b[i]
{
  result := [];
  var i: nat := 0;

  while i < |a|
    // i stays within array bounds
    invariant i <= |a|
    // The accumulator array keeps the correct size.
    invariant |result| == i
    // Elements already processed (k < i) satisfy the modulo specification.
    invariant forall k :: 0 <= k < i ==> result[k] == a[k] % b[k]
  {
    // Safe since i < |a| and |a| == |b| from precondition
    // Also b[i] != 0 from allNonzero(b)
    result := result + [a[i] % b[i]];
    i := i + 1;
  }
}
