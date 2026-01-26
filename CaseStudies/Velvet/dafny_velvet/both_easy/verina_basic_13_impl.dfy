/* Problem Description
    cubeElements: Replace every element of an integer array with its cube.
    Natural language breakdown:
    1. Input is an array of integers (possibly empty).
    2. Output is an array of integers with the same size as the input.
    3. For each valid index i, the output element at i equals the cube of the input element at i.
    4. Cubing means multiplying the element by itself three times: x * x * x.
    5. There are no additional preconditions; the function must work for any array.
*/

// Helper: integer cube function
function intCube(x: int): int
{
  x * x * x
}

// Precondition: no requirements
predicate precondition(a: seq<int>)
{
  true
}

// Postcondition: size preserved and pointwise cube relation
predicate postcondition(a: seq<int>, result: seq<int>)
{
  |result| == |a| && (forall i :: 0 <= i < |a| ==> result[i] == intCube(a[i]))
}

method cubeElements(a: seq<int>) returns (result: seq<int>)
  requires precondition(a)
  ensures postcondition(a, result)
{
  result := [];
  var i: nat := 0;

  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == intCube(a[k])
  {
    result := result + [intCube(a[i])];
    i := i + 1;
  }
}

