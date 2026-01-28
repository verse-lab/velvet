/*
  Problem Description:
    isSublist: decide whether `sub` appears as a contiguous block inside `main`.
    Natural language breakdown:
    1. Input consists of two lists of integers: `sub` and `main`.
    2. `sub` appears in `main` as a contiguous sequence iff there exist lists `pre` and `suf`
       such that `main = pre ++ sub ++ suf`.
    3. The method returns `true` exactly when `sub` is a contiguous sublist (infix) of `main`.
    4. The empty list is a contiguous sublist of every list, including the empty list.
    5. If `main` is empty and `sub` is nonempty, the answer is `false`.
    6. There are no preconditions.
*/

// Helper predicate: `sub` is a contiguous sublist (infix) of `main`.
// Equivalent to Lean's `List.IsInfix` with notation `<:+:`.
ghost predicate isContiguousSublist(sub: seq<int>, main: seq<int>)
{
  exists pre: seq<int>, suf: seq<int> :: main == pre + sub + suf
}

// Lemma: empty sequence is an infix of any sequence
lemma emptyIsInfix(main: seq<int>)
  ensures isContiguousSublist([], main)
{
  assert main == [] + [] + main;
}

// Lemma: any sequence is an infix of itself
lemma selfIsInfix(s: seq<int>)
  ensures isContiguousSublist(s, s)
{
  assert s == [] + s + [];
}

// Lemma: if rest is an infix of main, then rest[1..] is also an infix of main
lemma tailPreservesInfix(rest: seq<int>, main: seq<int>)
  requires |rest| > 0
  requires isContiguousSublist(rest, main)
  ensures isContiguousSublist(rest[1..], main)
{
  var pre, suf :| main == pre + rest + suf;
  assert main == (pre + [rest[0]]) + rest[1..] + suf;
}

// Lemma: if sub is a prefix of rest and rest is an infix of main, then sub is an infix of main
lemma prefixOfInfixIsInfix(sub: seq<int>, rest: seq<int>, main: seq<int>)
  requires |sub| <= |rest|
  requires sub == rest[..|sub|]
  requires isContiguousSublist(rest, main)
  ensures isContiguousSublist(sub, main)
{
  var pre, suf :| main == pre + rest + suf;
  assert rest == sub + rest[|sub|..];
  assert main == pre + sub + (rest[|sub|..] + suf);
}

// Lemma: if sub is an infix of main starting at some position in rest,
// and sub != rest[..|sub|], then sub must be an infix of rest[1..]
lemma infixShiftLemma(sub: seq<int>, rest: seq<int>, main: seq<int>)
  requires |rest| > 0
  requires |sub| > 0
  requires isContiguousSublist(sub, main)
  requires isContiguousSublist(rest, main)
  requires isContiguousSublist(sub, rest)
  requires |sub| <= |rest| ==> sub != rest[..|sub|]
  ensures isContiguousSublist(sub, rest[1..])
{
  var pre, suf :| rest == pre + sub + suf;
  if pre == [] {
    // sub is a prefix of rest, contradicts sub != rest[..|sub|]
    assert rest == sub + suf;
    assert rest[..|sub|] == sub;
    assert |sub| <= |rest|;
    assert false;
  } else {
    // pre is non-empty, so sub appears after first element
    assert rest == [pre[0]] + (pre[1..] + sub + suf);
    assert rest[1..] == pre[1..] + sub + suf;
  }
}

method isSublist(sub: seq<int>, main: seq<int>) returns (result: bool)
  ensures result == true <==> isContiguousSublist(sub, main)
{
  // Empty list is an infix of any list.
  if sub == [] {
    emptyIsInfix(main);
    return true;
  } else {
    var rest := main;
    var found := false;

    selfIsInfix(main);

    while rest != [] && found == false
      // Invariant 1: `rest` is always an infix of the original `main`.
      // Init: rest = main.
      // Preserved: dropping 1 element from a list preserves being an infix of the original.
      invariant isContiguousSublist(rest, main)
      // Invariant 2: Soundness of `found`: if we ever set it to true, then `sub` is indeed an infix of `main`.
      // Init: found = false, so vacuously true. Preserved: only set to true when sub = rest.take sub.length,
      // and since rest is an infix of main, a prefix of rest is also an infix of main.
      invariant found == true ==> isContiguousSublist(sub, main)
      // Invariant 3: Completeness w.r.t. current suffix: if `sub` is an infix of `main`, then either we already found it
      // or it is still an infix of the remaining `rest` (some later start position).
      // Init: rest = main, found = false. Preserved: if not found at current head position, rest := rest.drop 1.
      invariant isContiguousSublist(sub, main) ==> found == true || isContiguousSublist(sub, rest)
      decreases |rest|, !found
    {
      // If sub is longer than remaining suffix, it cannot match here.
      if |sub| <= |rest| {
        if sub == rest[..|sub|] {
          prefixOfInfixIsInfix(sub, rest, main);
          found := true;
        } else {
          // Need to prove: sub is still an infix of rest[1..] if it was an infix of rest
          ghost var oldRest := rest;
          if isContiguousSublist(sub, main) && !found {
            infixShiftLemma(sub, rest, main);
          }
          tailPreservesInfix(rest, main);
          rest := rest[1..];
        }
      } else {
        tailPreservesInfix(rest, main);
        rest := rest[1..];
      }
    }
    return found;
  }
}
