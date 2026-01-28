// Problem Description
//   toUppercase: Convert a string to uppercase.
//   Natural language breakdown:
//   1. Input is a string s.
//   2. Output is a string result.
//   3. The output has the same length as the input.
//   4. For every position i within bounds, the i-th character of result equals
//      the uppercase of the i-th character of s.
//   5. Uppercasing is performed using Char.ToUpper: lowercase ASCII letters are
//      mapped to their corresponding uppercase letters; all other characters are unchanged.
//   6. There are no preconditions.

predicate precondition(s: string)
{
  true
}

// Helper to convert char to uppercase
function charToUpper(c: char): char
{
  if 'a' <= c <= 'z' then
    (c as int - 'a' as int + 'A' as int) as char
  else
    c
}

predicate postcondition(s: string, result: string)
{
  |result| == |s| &&
  (forall i :: 0 <= i < |s| ==> result[i] == charToUpper(s[i]))
}

method toUppercase(s: string) returns (result: string)
  requires precondition(s)
  ensures postcondition(s, result)
{
  result := "";
  var i: nat := 0;

  while i < |s|
    // i stays within bounds
    invariant i <= |s|
    // result is exactly the mapped prefix (toUpper) of the first i characters of s
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == charToUpper(s[j])
  {
    result := result + [charToUpper(s[i])];
    i := i + 1;
  }
}
