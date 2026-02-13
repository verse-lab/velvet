// Problem Description
//   removeElement: remove the element at index k from an array of integers.
//   Natural language breakdown:
//   1. Inputs are an integer array s and a natural number k (0-indexed).
//   2. k is assumed to be a valid index, i.e., 0 ≤ k < s.size.
//   3. The output is an array containing all elements of s except the one at index k.
//   4. Elements before index k are unchanged and keep their positions.
//   5. Elements after index k are shifted left by one position.
//   6. The output array has size exactly s.size - 1.

method removeElement(s: seq<int>, k: nat) returns (result: seq<int>)
  requires k < |s|
  ensures |result| + 1 == |s|
  ensures (forall i :: 0 <= i < |result| ==>
            (if i < k then result[i] == s[i] else result[i] == s[i + 1]))
{
  result := s[..k] + s[k+1..];
}
