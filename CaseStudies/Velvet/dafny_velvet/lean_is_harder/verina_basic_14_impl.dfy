/* Problem Description
    containsZ: Determine whether a given string contains the character 'z' or 'Z'.
    Natural language breakdown:
    1. Input is a string s.
    2. The method returns a Boolean.
    3. The result is true exactly when s contains at least one character equal to 'z' or equal to 'Z'.
    4. Otherwise the result is false.
    5. There are no preconditions.
*/

// Helper predicate: the string contains 'z' or 'Z'
predicate hasZ(s: string)
{
  exists i :: 0 <= i < |s| && (s[i] == 'z' || s[i] == 'Z')
}

// Precondition: no requirements
predicate precondition(s: string)
{
  true
}

// Postcondition: result is true iff s contains 'z' or 'Z'
predicate postcondition(s: string, result: bool)
{
  result == hasZ(s)
}

method containsZ(s: string) returns (result: bool)
  requires precondition(s)
  ensures postcondition(s, result)
{
  var found := false;
  var i: nat := 0;

  while i < |s| && !found
    invariant 0 <= i <= |s|
    invariant found <==> exists j :: 0 <= j < i && (s[j] == 'z' || s[j] == 'Z')
  {
    if s[i] == 'z' || s[i] == 'Z' {
      found := true;
    }
    i := i + 1;
  }

  result := found;
}

