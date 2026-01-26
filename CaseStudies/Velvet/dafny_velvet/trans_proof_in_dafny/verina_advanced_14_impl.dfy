/* Problem Description
    ifPowerOfFour: Determine whether a natural number is a power of four
    Natural language breakdown:
    1. A natural number n is a power of four if there exists a natural number x such that n = 4^x
    2. Powers of four are: 1 (4^0), 4 (4^1), 16 (4^2), 64 (4^3), 256 (4^4), 1024 (4^5), ...
    3. 0 is NOT a power of four (there is no x such that 4^x = 0)
    4. 1 is a power of four (4^0 = 1)
    5. Numbers like 2, 3, 8, etc. are not powers of four
    6. The function returns true if n is a power of four, false otherwise

    Key observations:
    - 4^x is always positive for any natural x, so 0 is never a power of four
    - We need to check if n can be expressed as 4^x for some natural x
    - This is equivalent to checking if n = (2^2)^x = 2^(2x), i.e., n is a power of 2 with even exponent
*/

// Helper function for power computation
function power(base: nat, exp: nat): nat
  decreases exp
{
  if exp == 0 then 1 else base * power(base, exp - 1)
}

// Lemma: powers of 4 are always positive
lemma PowerOfFourPositive(x: nat)
  ensures power(4, x) > 0
{
  if x == 0 {
    assert power(4, 0) == 1;
  } else {
    PowerOfFourPositive(x - 1);
    assert power(4, x) == 4 * power(4, x - 1);
  }
}

// Predicate: n is a power of four if there exists some natural x where 4^x = n
ghost predicate isPowerOfFour(n: nat)
{
  exists x: nat :: power(4, x) == n
}

// Postcondition: result is true iff n is a power of four
ghost predicate ensures1(n: nat, result: bool)
{
  result == true <==> isPowerOfFour(n)
}

// Precondition: no requirements
ghost predicate precondition(n: nat)
{
  true
}

// Postcondition wrapper
ghost predicate postcondition(n: nat, result: bool)
{
  ensures1(n, result)
}

// Helper lemma: if current is divisible by 4 and current is a power of 4, then current/4 is also a power of 4
lemma PowerOfFourDivision(current: nat)
  requires current > 1
  requires current % 4 == 0
  requires isPowerOfFour(current)
  ensures isPowerOfFour(current / 4)
{
  ghost var x :| power(4, x) == current;

  if x == 0 {
    assert power(4, 0) == 1;
    assert current == 1;
    assert false; // contradiction with current > 1
  }

  assert x > 0;
  var x1 := x - 1;
  assert x1 >= 0;
  assert power(4, x) == 4 * power(4, x1);
  assert current == 4 * power(4, x1);
  assert current / 4 == power(4, x1);
  assert isPowerOfFour(current / 4);
}

// Helper lemma: if current/4 is a power of 4 and current is divisible by 4, then current is a power of 4
lemma PowerOfFourMultiplication(current: nat)
  requires current % 4 == 0
  requires current > 0
  requires isPowerOfFour(current / 4)
  ensures isPowerOfFour(current)
{
  ghost var x: nat :| power(4, x) == current / 4;
  assert current == 4 * (current / 4);
  assert current == 4 * power(4, x);
  assert current == power(4, x + 1);
  assert isPowerOfFour(current);
}

// Lemma: 1 is a power of four
lemma OneIsPowerOfFour()
  ensures isPowerOfFour(1)
{
  assert power(4, 0) == 1;
}

// Lemma: if n is not 1 and not divisible by 4, then it's not a power of four
lemma NotOneNotDivisibleNotPower(n: nat)
  requires n != 1
  requires n % 4 != 0 || n == 0
  ensures !isPowerOfFour(n)
{
  if n == 0 {
    // 0 is never a power of 4
    forall x: nat
      ensures power(4, x) != 0
    {
      PowerOfFourPositive(x);
    }
  } else if n % 4 != 0 {
    // n > 0 and n % 4 != 0
    // For any x > 0, 4^x is divisible by 4
    // Only 4^0 = 1 is not divisible by 4
    forall x: nat | x > 0
      ensures power(4, x) % 4 == 0
    {
      assert power(4, x) == 4 * power(4, x - 1);
    }

    if isPowerOfFour(n) {
      ghost var x :| power(4, x) == n;
      if x == 0 {
        assert power(4, 0) == 1;
        assert n == 1;
        assert false; // contradiction with n != 1
      } else {
        assert power(4, x) % 4 == 0;
        assert n % 4 == 0;
        assert false; // contradiction
      }
    }
  }
}

// Main method
method ifPowerOfFour(n: nat) returns (result: bool)
  requires precondition(n)
  ensures postcondition(n, result)
{
  if n == 0 {
    result := false;
    // 0 is not a power of four
    assert !isPowerOfFour(0) by {
      forall x: nat
        ensures power(4, x) != 0
      {
        PowerOfFourPositive(x);
      }
    }
  } else {
    var current := n;

    while current > 1 && current % 4 == 0
      // Invariant 1: current is positive (we started with n > 0 and only divide)
      invariant current > 0
      // Invariant 2: n is a power of 4 iff current is a power of 4
      invariant isPowerOfFour(n) <==> isPowerOfFour(current)
      decreases current
    {
      // Maintain invariant through division
      ghost var oldCurrent := current;
      current := current / 4;

      // Prove invariant preservation
      if isPowerOfFour(oldCurrent) {
        PowerOfFourDivision(oldCurrent);
        assert isPowerOfFour(current);
      }
      if isPowerOfFour(current) {
        PowerOfFourMultiplication(oldCurrent);
        assert isPowerOfFour(oldCurrent);
      }
    }

    result := (current == 1);

    // Prove postcondition
    if current == 1 {
      OneIsPowerOfFour();
      assert isPowerOfFour(current);
    } else {
      NotOneNotDivisibleNotPower(current);
      assert !isPowerOfFour(current);
    }
  }
}