// Problem Description
//   isPrime: Determine whether a given natural number is prime.
//   Natural language breakdown:
//   1. The input is a natural number n, and the task assumes n ≥ 2.
//   2. A natural number n is prime iff it has no divisor k with 1 < k < n.
//   3. Equivalently: n is prime iff for every k with 1 < k < n, k does not divide n.
//   4. The method returns a Bool: true exactly when n is prime, and false otherwise.
//   5. Inputs that violate n ≥ 2 are outside the intended domain.

// Helper predicate: "n has a nontrivial divisor"
predicate HasNontrivialDivisor(n: nat)
{
  exists k: nat :: 1 < k < n && n % k == 0
}

// Precondition: input is expected to satisfy n ≥ 2.
predicate precondition(n: nat)
{
  2 <= n
}

// Postcondition: result is true iff there is no nontrivial divisor.
predicate postcondition(n: nat, result: bool)
{
  result == true <==> !HasNontrivialDivisor(n)
}

method isPrime(n: nat) returns (result: bool)
  requires precondition(n)
  ensures postcondition(n, result)
{
  // Brute-force check for any divisor k with 2 ≤ k < n.
  // If we find one, n is composite.
  var k: nat := 2;
  var composite: bool := false;

  while k < n && composite == false
    // Invariant: k stays within bounds
    invariant 2 <= k <= n
    // Invariant: when we mark composite, we have actually found a nontrivial divisor of n.
    invariant composite == true ==> (exists d: nat :: 1 < d < n && n % d == 0)
    // Invariant: if we have not marked composite yet, then no nontrivial divisor has been found
    // among all candidates in [2, k).
    invariant composite == false ==> (forall d: nat :: 2 <= d < k ==> n % d != 0)
    decreases n - k
  {
    if n % k == 0 {
      composite := true;
      break;
    }
    k := k + 1;
  }

  if composite == true {
    result := false;
  } else {
    result := true;
  }
}