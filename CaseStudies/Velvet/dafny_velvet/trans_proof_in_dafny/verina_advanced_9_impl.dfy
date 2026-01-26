/* Problem Description
    countSumDivisibleBy: Count numbers smaller than n whose digit sum is divisible by d
    Natural language breakdown:
    1. Given a natural number n and a divisor d (where d > 0)
    2. For each number k in the range [0, n), compute the sum of its digits
    3. Check if this digit sum is divisible by d
    4. Count how many such numbers satisfy this divisibility condition
    5. The digit sum of a number is the sum of all its decimal digits
       - e.g., digitSum(123) = 1 + 2 + 3 = 6
    6. A number's digit sum is divisible by d if d | digitSum(k)
    7. Edge cases:
       - n = 0: no numbers to check, result is 0
       - n = 1: only check 0, digitSum(0) = 0, d | 0 always, so result is 1
       - d = 1: all digit sums are divisible by 1, result is n
*/

// Helper function to compute the sum of digits of a natural number
// This is a standard mathematical concept that requires recursion
function digitSum(n: nat): nat
  decreases n
{
  if n < 10 then n
  else (n % 10) + digitSum(n / 10)
}

// Helper function to count numbers in [0, k) whose digit sum is divisible by d
function countDivisibleInRange(k: nat, d: nat): nat
  requires d > 0
  decreases k
{
  if k == 0 then 0
  else if digitSum(k-1) % d == 0 then countDivisibleInRange(k-1, d) + 1
  else countDivisibleInRange(k-1, d)
}

// Lemma: Adding an element that satisfies the condition increases count by 1
lemma CountIncrementWhenDivisible(k: nat, d: nat)
  requires d > 0
  requires k >= 0
  requires digitSum(k) % d == 0
  ensures countDivisibleInRange(k+1, d) == countDivisibleInRange(k, d) + 1
{
  // By definition of countDivisibleInRange
  assert countDivisibleInRange(k+1, d) ==
    (if digitSum(k) % d == 0 then countDivisibleInRange(k, d) + 1
     else countDivisibleInRange(k, d));
}

// Lemma: Adding an element that doesn't satisfy the condition doesn't change count
lemma CountSameWhenNotDivisible(k: nat, d: nat)
  requires d > 0
  requires k >= 0
  requires digitSum(k) % d != 0
  ensures countDivisibleInRange(k+1, d) == countDivisibleInRange(k, d)
{
  // By definition of countDivisibleInRange
  assert countDivisibleInRange(k+1, d) ==
    (if digitSum(k) % d == 0 then countDivisibleInRange(k, d) + 1
     else countDivisibleInRange(k, d));
}

// Precondition: d must be positive
ghost predicate precondition(n: nat, d: nat)
{
  d > 0
}

// Postcondition: result equals the cardinality of the set of numbers in [0, n)
// whose digit sum is divisible by d
// Using countDivisibleInRange for a property-based specification
ghost predicate postcondition(n: nat, d: nat, result: nat)
  requires d > 0
{
  result == countDivisibleInRange(n, d)
}

// Main method
method countSumDivisibleBy(n: nat, d: nat) returns (result: nat)
  requires precondition(n, d)
  ensures postcondition(n, d, result)
{
  var count := 0;
  var k := 0;

  while k < n
    // Invariant 1: k is bounded by n
    // Init: k starts at 0, so 0 <= k <= n holds
    // Preservation: k increments by 1 each iteration, loop guard ensures k < n before increment, so k+1 <= n
    // Sufficiency: when k = n, we've processed all numbers in [0, n)
    invariant 0 <= k <= n
    // Invariant 2: count equals the number of integers in [0, k) with digit sum divisible by d
    // Init: k = 0, count = 0, countDivisibleInRange(0, d) = 0
    // Preservation: if digitSum k divisible by d, count increases by 1, matching the function
    // Sufficiency: at k = n, count = countDivisibleInRange(n, d) = postcondition
    invariant count == countDivisibleInRange(k, d)
  {
    var sum := digitSum(k);
    if sum % d == 0 {
      CountIncrementWhenDivisible(k, d);
      count := count + 1;
    } else {
      CountSameWhenNotDivisible(k, d);
    }
    k := k + 1;
  }

  result := count;
}