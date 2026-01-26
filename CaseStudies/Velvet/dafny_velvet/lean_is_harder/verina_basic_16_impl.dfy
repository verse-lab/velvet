/* Problem Description
    replaceChars: Replace every occurrence of a specified character in a string.
    Natural language breakdown:
    1. Inputs are a string s and two characters oldChar and newChar.
    2. The result is a string with the same number of characters as s.
    3. For each index i within bounds, if the i-th character of s equals oldChar,
       then the i-th character of the result equals newChar.
    4. For each index i within bounds, if the i-th character of s does not equal oldChar,
       then the i-th character of the result equals the i-th character of s.
    5. There are no preconditions; the method must work for any string and characters.
*/

// Helper: pointwise replacement on characters
function replChar(oldChar: char, newChar: char, c: char): char
{
  if c == oldChar then newChar else c
}

// Precondition: no requirements
predicate precondition(s: string, oldChar: char, newChar: char)
{
  true
}

// Postcondition: same length and pointwise replacement behavior
predicate postcondition(s: string, oldChar: char, newChar: char, result: string)
{
  |result| == |s| &&
  (forall i :: 0 <= i < |s| ==> result[i] == replChar(oldChar, newChar, s[i]))
}

method replaceChars(s: string, oldChar: char, newChar: char) returns (result: string)
  requires precondition(s, oldChar, newChar)
  ensures postcondition(s, oldChar, newChar, result)
{
  result := "";
  var i: nat := 0;

  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == replChar(oldChar, newChar, s[j])
  {
    var c := s[i];
    var c' := replChar(oldChar, newChar, c);
    result := result + [c'];
    i := i + 1;
  }
}

