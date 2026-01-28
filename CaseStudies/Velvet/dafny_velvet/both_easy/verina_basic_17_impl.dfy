/* Problem Description
    toLowercase: Convert all uppercase characters in a string to their lowercase equivalents.
    Natural language breakdown:
    1. Input is any string s (no preconditions).
    2. Output is a string result with the same length as s.
    3. For every character position i in s, the output character at i equals Char.toLower applied to the input character at i.
    4. Characters not affected by Char.toLower remain unchanged.
*/

// Helper function to convert a character to lowercase
function toLowerChar(c: char): char
{
  if 'A' <= c <= 'Z' then
    c + ('a' - 'A' as char)
  else
    c
}

// Helper: Pointwise character relation between two strings
// This characterizes the output uniquely without referring to String.toLower
// Note: Char.toLower converts uppercase ASCII letters 'A'..'Z' to lowercase and leaves other chars unchanged
predicate charsLoweredPointwise(s: seq<char>, t: seq<char>)
{
  |t| == |s| &&
  forall i :: 0 <= i < |s| ==> t[i] == toLowerChar(s[i])
}

predicate precondition(s: seq<char>)
{
  true
}

predicate postcondition(s: seq<char>, result: seq<char>)
{
  charsLoweredPointwise(s, result)
}

method toLowercase(s: seq<char>) returns (result: seq<char>)
  requires precondition(s)
  ensures postcondition(s, result)
{
  var tl: seq<char> := [];
  var i: nat := 0;

  while i < |s|
    // i stays within bounds of the source list
    // init: i=0; step: i:=i+1; exit: i=|s|
    invariant i <= |s|
    // tl is exactly the lowered prefix of s of length i
    // init: tl=[] and i=0; step: append lowered s[i]
    invariant |tl| == i
    invariant forall j :: 0 <= j < i ==> tl[j] == toLowerChar(s[j])
  {
    var c := s[i];
    tl := tl + [toLowerChar(c)];
    i := i + 1;
  }

  result := tl;
}

