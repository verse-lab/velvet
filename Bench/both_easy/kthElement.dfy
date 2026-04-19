/* Problem Description
    kthElement: Find the kth element in an array using 1-based indexing
    Natural language breakdown:
    1. Given an array of integers and a position k (1-based)
    2. The array is non-empty (size ≥ 1)
    3. The position k is valid: 1 ≤ k ≤ array.size
    4. We need to return the element at position k using 1-based indexing
    5. In 1-based indexing, the first element is at position 1, second at position 2, etc.
    6. The mapping is: 1-based position k corresponds to 0-based index (k-1)
    7. The result must be the array element at 0-based index (k-1)
    8. Examples:
       - arr = [10, 20, 30, 40, 50], k = 1 → result = 10 (first element)
       - arr = [10, 20, 30, 40, 50], k = 3 → result = 30 (third element)
       - arr = [10, 20, 30, 40, 50], k = 5 → result = 50 (last element)
    9. Edge cases:
       - Single element array: k must be 1, returns that element
       - k at boundary: k = 1 returns first, k = size returns last
*/

method kthElement(arr: seq<int>, k: nat) returns (result: int)
  requires |arr| >= 1
  requires 1 <= k
  requires k <= |arr|
  ensures result == arr[k - 1]
{
  result := arr[k - 1];
}

