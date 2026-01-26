/* Problem Description
    cubeSurfaceArea: compute the surface area of a cube from its edge length.

    Natural language breakdown:
    1. The input is a natural number `size`, the length of an edge of a cube.
    2. The surface area of a cube equals 6 times the area of one face.
    3. Each face is a square with area `size ^ 2`.
    4. Therefore, the surface area equals `6 * (size ^ 2)`.
    5. The output is a natural number.
    6. There are no rejected inputs.
*/

// Precondition: no requirements
predicate precondition(size: nat)
{
  true
}

// Postcondition: result is 6 times the square of the size
predicate postcondition(size: nat, result: nat)
{
  result == 6 * (size * size)
}

method cubeSurfaceArea(size: nat) returns (result: nat)
  requires precondition(size)
  ensures postcondition(size, result)
{
  var area := 6 * (size * size);
  result := area;
}

