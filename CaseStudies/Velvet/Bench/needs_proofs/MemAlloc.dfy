// Faithful translation of MemAlloc.lean (Velvet/Loom memory allocator)
//
// Key translation decisions:
// - Lean's total function `addr → addr` becomes `map<int, int>` with domain requirements
// - `Function.update h u v` becomes `next[u := v]` (map update)
// - `List.find?` becomes `FindFirst` returning `Option<int>`
// - `List.erase` becomes `Erase` on sequences
// - Ghost parameter `Ps` is a ghost sequence in the method signature
// - `mut` parameters become return values since Dafny doesn't have mutable parameters

type addr = int

// ---------------------------------------------------------------------------
// Core predicates
// ---------------------------------------------------------------------------

predicate path(h: map<addr, addr>, x: addr, l: seq<addr>, y: addr)
  decreases l
{
  if |l| == 0 then
    x == y
  else
    l[0] != 0 && x == l[0] && l[0] in h && path(h, h[l[0]], l[1..], y)
}

predicate distinct(l: seq<addr>)
  decreases l
{
  if |l| == 0 then
    true
  else
    l[0] !in l[1..] && distinct(l[1..])
}

predicate distPath(h: map<addr, addr>, x: addr, l: seq<addr>, y: addr)
{
  path(h, x, l, y) && distinct(l)
}

predicate domainCovers(h: map<addr, addr>, l: seq<addr>)
{
  forall a :: a in l ==> a in h
}

// ---------------------------------------------------------------------------
// Helper functions
// ---------------------------------------------------------------------------

datatype Option<T> = None | Some(value: T)

function FindFirst(l: seq<addr>, block_size: addr -> nat, size: nat): Option<addr>
  decreases l
{
  if |l| == 0 then None
  else if block_size(l[0]) >= size then Some(l[0])
  else FindFirst(l[1..], block_size, size)
}

function Erase(l: seq<addr>, b: addr): seq<addr>
  decreases l
{
  if |l| == 0 then []
  else if l[0] == b then l[1..]
  else [l[0]] + Erase(l[1..], b)
}

// ---------------------------------------------------------------------------
// Structural lemmas about path and distinct
// ---------------------------------------------------------------------------

// All elements of a path are in the map's domain
lemma path_domain(h: map<addr, addr>, x: addr, l: seq<addr>, y: addr)
  requires path(h, x, l, y)
  ensures domainCovers(h, l)
  decreases l
{
  if |l| > 0 {
    path_domain(h, h[l[0]], l[1..], y);
  }
}

// Positional access into a path
lemma path_index(h: map<addr, addr>, x: addr, l: seq<addr>, y: addr, i: nat)
  requires path(h, x, l, y)
  requires 0 <= i < |l|
  ensures l[i] in h
  ensures l[i] != 0
  ensures i + 1 < |l| ==> h[l[i]] == l[i + 1]
  ensures i + 1 == |l| ==> h[l[i]] == y
  decreases i
{
  if i == 0 {
    // Directly from path(h, x, l, y) with |l| > 0
    if |l| == 1 {
      // path(h, h[l[0]], [], y) => h[l[0]] == y
    } else {
      // path(h, h[l[0]], l[1..], y) => l[1..][0] == l[1], h[l[0]] == l[1]
    }
  } else {
    path_index(h, h[l[0]], l[1..], y, i - 1);
  }
}

// Concatenating two paths yields a path
lemma path_append(h: map<addr, addr>, x: addr, y: addr, z: addr,
                  l1: seq<addr>, l2: seq<addr>)
  requires path(h, x, l1, y)
  requires path(h, y, l2, z)
  ensures path(h, x, l1 + l2, z)
  decreases l1
{
  path_domain(h, x, l1, y);
  if |l1| == 0 {
    assert l1 + l2 == l2;
  } else {
    path_append(h, h[l1[0]], y, z, l1[1..], l2);
    assert (l1 + l2)[0] == l1[0];
    assert (l1 + l2)[1..] == l1[1..] + l2;
  }
}

// Splitting a concatenated path
lemma path_split(h: map<addr, addr>, x: addr, y: addr,
                 l1: seq<addr>, l2: seq<addr>)
  requires path(h, x, l1 + l2, y)
  ensures exists z :: path(h, x, l1, z) && path(h, z, l2, y)
  decreases l1
{
  if |l1| == 0 {
    assert l1 + l2 == l2;
  } else {
    assert (l1 + l2)[0] == l1[0];
    assert (l1 + l2)[1..] == l1[1..] + l2;
    path_split(h, h[l1[0]], y, l1[1..], l2);
  }
}

// Path uniqueness: same list, same endpoint
lemma path_function(h: map<addr, addr>, x: addr, y1: addr, y2: addr,
                    l: seq<addr>)
  requires path(h, x, l, y1)
  requires path(h, x, l, y2)
  ensures y1 == y2
  decreases l
{
  if |l| > 0 {
    path_function(h, h[l[0]], y1, y2, l[1..]);
  }
}

// 0 is never a node in a path
lemma path_zero_not_mem(h: map<addr, addr>, x: addr, y: addr, l: seq<addr>)
  requires path(h, x, l, y)
  ensures 0 !in l
  decreases l
{
  if |l| > 0 {
    path_zero_not_mem(h, h[l[0]], y, l[1..]);
  }
}

// Two paths from same origin to 0 must be identical
lemma path_zero_unique(h: map<addr, addr>, x: addr,
                       l1: seq<addr>, l2: seq<addr>)
  requires path(h, x, l1, 0)
  requires path(h, x, l2, 0)
  ensures l1 == l2
  decreases l1, l2
{
  if |l1| == 0 && |l2| == 0 {
  } else if |l1| == 0 {
    // x == 0 but l2[0] != 0 && x == l2[0] — contradiction
  } else if |l2| == 0 {
    // symmetric contradiction
  } else {
    assert l1[0] == l2[0];
    path_zero_unique(h, h[l1[0]], l1[1..], l2[1..]);
  }
}

// If there's a path to y != 0 and a path to 0, the path to 0 extends the path to y
lemma path_prefix_of_path_to_zero(h: map<addr, addr>, x: addr, y: addr,
                                  l1: seq<addr>, l2: seq<addr>)
  requires path(h, x, l1, y)
  requires path(h, x, l2, 0)
  requires y != 0
  ensures exists t :: l2 == l1 + [y] + t
  decreases l1, l2
{
  if |l1| == 0 {
    if |l2| == 0 {
      // x == 0 contradicts x == y != 0
    } else {
      assert l2[0] == y;
      assert l2 == [y] + l2[1..];
      assert [] + [y] + l2[1..] == [y] + l2[1..];
    }
  } else {
    if |l2| == 0 {
      // x == 0 contradicts l1[0] != 0 && x == l1[0]
    } else {
      assert l1[0] == l2[0];
      path_prefix_of_path_to_zero(h, h[l1[0]], y, l1[1..], l2[1..]);
      var t :| l2[1..] == l1[1..] + [y] + t;
      calc {
        l2;
        == [l2[0]] + l2[1..];
        == [l1[0]] + (l1[1..] + [y] + t);
        == l1 + [y] + t;
      }
    }
  }
}

// distinct distributes over append
lemma distinct_append(l1: seq<addr>, l2: seq<addr>)
  ensures distinct(l1 + l2) <==>
    (distinct(l1) && distinct(l2) && forall x :: x in l1 ==> x !in l2)
  decreases l1
{
  if |l1| == 0 {
    assert l1 + l2 == l2;
  } else {
    distinct_append(l1[1..], l2);
    assert (l1 + l2)[0] == l1[0];
    assert (l1 + l2)[1..] == l1[1..] + l2;
    // Help Z3 with membership in concatenated sequences
    assert forall x :: x in l1[1..] + l2 <==> x in l1[1..] || x in l2;
    assert forall x :: x in l1 <==> x == l1[0] || x in l1[1..];
  }
}

// Updating a pointer not in the path doesn't change the path
lemma path_update_of_not_mem(h: map<addr, addr>, x: addr, y: addr,
                             u: addr, v: addr, l: seq<addr>)
  requires path(h, x, l, y)
  requires u !in l
  ensures path(h[u := v], x, l, y)
  decreases l
{
  path_domain(h, x, l, y);
  if |l| > 0 {
    assert l[0] != u;
    assert h[u := v][l[0]] == h[l[0]];
    path_update_of_not_mem(h, h[l[0]], y, u, v, l[1..]);
  }
}

// Erase of an element in the middle of a distinct list
lemma erase_middle_unique(l1: seq<addr>, l2: seq<addr>, p: addr)
  requires distinct(l1 + [p] + l2)
  ensures Erase(l1 + [p] + l2, p) == l1 + l2
  decreases l1
{
  assert l1 + [p] + l2 == l1 + ([p] + l2);
  distinct_append(l1, [p] + l2);
  if |l1| == 0 {
    assert l1 + [p] + l2 == [p] + l2;
    assert l1 + l2 == l2;
  } else {
    assert l1[0] in l1;
    // From distinct_append: forall x :: x in l1 ==> x !in ([p] + l2)
    assert forall x :: x in l1 ==> x !in ([p] + l2);
    assert l1[0] != p;
    assert (l1 + [p] + l2)[0] == l1[0];
    assert (l1 + [p] + l2)[1..] == l1[1..] + [p] + l2;
    erase_middle_unique(l1[1..], l2, p);
  }
}

// FindFirst over a split list where all of l1 fail the predicate
lemma find_in_split(l1: seq<addr>, l2: seq<addr>, b: addr,
                    block_size: addr -> nat, size: nat)
  requires forall x :: x in l1 ==> block_size(x) < size
  requires block_size(b) >= size
  ensures FindFirst(l1 + [b] + l2, block_size, size) == Some(b)
  decreases l1
{
  if |l1| == 0 {
    assert l1 + [b] + l2 == [b] + l2;
  } else {
    assert (l1 + [b] + l2)[0] == l1[0];
    assert l1[0] in l1;
    assert block_size(l1[0]) < size;
    assert (l1 + [b] + l2)[1..] == l1[1..] + [b] + l2;
    find_in_split(l1[1..], l2, b, block_size, size);
  }
}

// If all elements fail the predicate, FindFirst returns None
lemma find_none_if_all_fail(l: seq<addr>, block_size: addr -> nat, size: nat)
  requires forall x :: x in l ==> block_size(x) < size
  ensures FindFirst(l, block_size, size) == None
  decreases l
{
  if |l| > 0 {
    assert l[0] in l;
    find_none_if_all_fail(l[1..], block_size, size);
  }
}

// Distinct prefix: if l1 ++ [a] ++ l2 is distinct, then l1 ++ [a] is distinct
lemma distinct_prefix(l1: seq<addr>, l2: seq<addr>, a: addr)
  requires distinct(l1 + [a] + l2)
  ensures distinct(l1 + [a])
  decreases l1
{
  if |l1| == 0 {
    assert l1 + [a] == [a];
  } else {
    assert (l1 + [a] + l2)[0] == l1[0];
    assert (l1 + [a] + l2)[1..] == l1[1..] + [a] + l2;
    distinct_prefix(l1[1..], l2, a);

    // Show distinct(l1 + [a])
    assert (l1 + [a])[0] == l1[0];
    assert (l1 + [a])[1..] == l1[1..] + [a];

    // l1[0] !in l1[1..] + [a]: from l1[0] !in l1[1..] + [a] + l2
    assert l1[0] !in (l1 + [a] + l2)[1..];
    assert l1[0] !in l1[1..] + [a] + l2;
    // l1[1..] + [a] is a subsequence of l1[1..] + [a] + l2
    assert forall x :: x in l1[1..] + [a] ==> x in l1[1..] + [a] + l2;
    assert l1[0] !in l1[1..] + [a];
  }
}

// Distinct sublist after erase
lemma distinct_erase(l: seq<addr>, b: addr)
  requires distinct(l)
  requires b in l
  ensures distinct(Erase(l, b))
  decreases l
{
  if |l| > 0 {
    if l[0] == b {
      // Erase returns l[1..], which is distinct
    } else {
      assert b in l[1..];
      distinct_erase(l[1..], b);
      // Erase(l, b) = [l[0]] + Erase(l[1..], b)
      // Need: l[0] !in Erase(l[1..], b)
      erase_subset(l[1..], b);
    }
  }
}

// Elements of Erase(l, b) are a subset of elements of l
lemma erase_subset(l: seq<addr>, b: addr)
  ensures forall x :: x in Erase(l, b) ==> x in l
  decreases l
{
  if |l| > 0 && l[0] != b {
    erase_subset(l[1..], b);
  }
}

// Membership in FindFirst result implies membership in list
lemma find_mem(l: seq<addr>, block_size: addr -> nat, size: nat, b: addr)
  requires FindFirst(l, block_size, size) == Some(b)
  ensures b in l
  decreases l
{
  if |l| > 0 {
    if block_size(l[0]) >= size {
      assert b == l[0];
    } else {
      find_mem(l[1..], block_size, size, b);
    }
  }
}

// ---------------------------------------------------------------------------
// Skipping a node in a path (corresponds to path_update_skip in Lean)
// If path h x (Qs ++ [q] ++ [p] ++ Rest) 0 and we update h[q] := h[p],
// then path (h[q := h[p]]) x (Qs ++ [q] ++ Rest) 0
// ---------------------------------------------------------------------------
lemma path_update_skip(h: map<addr, addr>, x: addr, Qs: seq<addr>,
                       q: addr, p: addr, Rest: seq<addr>)
  requires path(h, x, Qs + [q] + [p] + Rest, 0)
  requires distinct(Qs + [q] + [p] + Rest)
  requires q != 0
  requires p != 0
  requires q in h
  requires p in h
  ensures path(h[q := h[p]], x, Qs + [q] + Rest, 0)
{
  // Sequence associativity helpers
  assert Qs + [q] + [p] + Rest == Qs + ([q] + [p] + Rest);
  assert Qs + [q] + [p] + Rest == (Qs + [q]) + ([p] + Rest);
  assert Qs + [q] + Rest == Qs + ([q] + Rest);

  // Split the path at Qs
  var after_q := [q] + [p] + Rest;
  path_split(h, x, 0, Qs, after_q);
  var z :| path(h, x, Qs, z) && path(h, z, after_q, 0);

  // z == q (from path(h, z, [q, p, ...], 0) => z == q)
  assert z == q;
  assert path(h, q, [q] + [p] + Rest, 0);

  // Extract path(h, h[p], Rest, 0) from the path through [q, p] ++ Rest
  // path(h, q, [q] + [p] + Rest, 0) =>
  //   q in h, h[q] == p (since [p]+Rest is next), path(h, p, [p] + Rest, 0)
  //   path(h, p, [p] + Rest, 0) => p in h, path(h, h[p], Rest, 0)
  assert [q] + [p] + Rest == [q] + ([p] + Rest);
  assert path(h, h[q], [p] + Rest, 0);
  assert h[q] == p;
  assert path(h, h[p], Rest, 0);

  // q !in Rest (from distinctness)
  assert (Qs + [q] + [p]) + Rest == Qs + [q] + [p] + Rest;
  distinct_append(Qs + [q] + [p], Rest);
  assert q in Qs + [q] + [p];
  assert q !in Rest;

  // path(h[q := h[p]], h[p], Rest, 0) — q not in Rest so update is irrelevant
  path_update_of_not_mem(h, h[p], 0, q, h[p], Rest);

  // Build path(h[q := h[p]], q, [q] + Rest, 0)
  assert h[q := h[p]][q] == h[p];
  assert q in h[q := h[p]];
  assert path(h[q := h[p]], h[p], Rest, 0);
  assert path(h[q := h[p]], q, [q] + Rest, 0);

  // q !in Qs (from distinctness)
  assert Qs + ([q] + [p] + Rest) == Qs + [q] + [p] + Rest;
  distinct_append(Qs, [q] + [p] + Rest);
  assert q in [q] + [p] + Rest;
  assert q !in Qs;

  // path(h[q := h[p]], x, Qs, q) — q not in Qs so update is irrelevant
  path_update_of_not_mem(h, x, q, q, h[p], Qs);

  // Combine
  path_append(h[q := h[p]], x, q, 0, Qs, [q] + Rest);
}

// ---------------------------------------------------------------------------
// The program: mem_alloc
// ---------------------------------------------------------------------------

method mem_alloc(
  saddr: addr -> addr,
  block_size: addr -> nat,
  next0: map<addr, addr>,
  free_list0: addr,
  size: nat,
  ghost Ps: seq<addr>
) returns (mem: addr, next: map<addr, addr>, free_list: addr)
  requires distPath(next0, free_list0, Ps, 0)
  requires domainCovers(next0, Ps)
  ensures forall b :: FindFirst(Ps, block_size, size) == Some(b) ==>
    mem == b && distPath(next, free_list, Erase(Ps, b), 0)
  decreases *
{
  next := next0;
  free_list := free_list0;

  // ---- Case 1: empty free list ----
  if free_list == 0 {
    // free_list == 0 implies Ps == [] (from path definition)
    assert |Ps| == 0;
    mem := 0;
    return;
  }

  // free_list != 0 implies Ps is non-empty and free_list == Ps[0]
  assert |Ps| > 0;
  assert Ps[0] == free_list;
  assert free_list in next;

  // ---- Case 2: first block fits ----
  if block_size(free_list) >= size {
    var res := free_list;
    free_list := next[free_list];
    mem := res;

    // Prove postcondition: FindFirst(Ps, ...) == Some(free_list0)
    // Since Ps[0] == free_list0 and block_size(free_list0) >= size
    assert FindFirst(Ps, block_size, size) == Some(free_list0);

    // Erase(Ps, free_list0) == Ps[1..] since Ps starts with free_list0
    assert Erase(Ps, free_list0) == Ps[1..];

    // path(next, next[free_list0], Ps[1..], 0) from original path
    assert path(next, next[free_list0], Ps[1..], 0);

    // distinct(Ps[1..]) from distinct(Ps)
    assert distinct(Ps[1..]);

    return;
  }

  // ---- Case 3: walk the list ----
  assert block_size(free_list) < size;

  var q := free_list;
  var p := next[free_list];

  // Ghost: track the path we've walked (all too small) and path to q
  ghost var Qs: seq<addr> := [free_list];  // path from free_list to p, all too small

  // Establish loop invariants
  assert path(next, free_list, [free_list], p);
  assert distinct([free_list]);
  assert distPath(next, free_list, [free_list], p);

  // Witness for exists Qs' :: distPath(next, free_list, Qs', q)
  // q == free_list, so Qs' = [] works
  assert path(next, free_list, [], free_list);
  ghost var empty: seq<addr> := [];
  assert distinct(empty);
  assert distPath(next, free_list, [], free_list);

  // p in domain check
  if |Ps| > 1 {
    path_index(next, free_list, Ps, 0, 0);
    assert next[Ps[0]] == Ps[1];
    assert p == Ps[1];
    assert p in next || p == 0;
  } else {
    path_index(next, free_list, Ps, 0, 0);
    assert p == 0;
  }

  while p != 0 && block_size(p) < size
    invariant distPath(next, free_list, Ps, 0)
    invariant distPath(next, free_list, Qs, p)
    invariant forall a :: a in Qs ==> block_size(a) < size
    invariant q in next
    invariant q != 0
    invariant p == next[q]
    invariant |Qs| > 0 && Qs[|Qs| - 1] == q
    invariant exists Qs' :: distPath(next, free_list, Qs', q)
    invariant domainCovers(next, Ps)
    invariant p != 0 ==> p in next
    decreases *
  {
    ghost var old_p := p;
    ghost var old_q := q;
    ghost var old_Qs := Qs;

    // p != 0 from loop condition, so p is in domain
    assert p in next;

    // Extend Qs with p
    // Need: path(next, free_list, Qs + [p], next[p])
    // From: path(next, free_list, Qs, p) and path(next, p, [p], next[p])
    assert path(next, p, [p], next[p]);
    path_append(next, free_list, p, next[p], Qs, [p]);
    assert path(next, free_list, Qs + [p], next[p]);

    // Need: distinct(Qs + [p])
    // p !in Qs: from distPath(next, free_list, Ps, 0) and distPath(next, free_list, Qs, p)
    // if p were in Qs, it would create a cycle in a distinct path to 0
    path_prefix_of_path_to_zero(next, free_list, p, Qs, Ps);
    ghost var tail :| Ps == Qs + [p] + tail;

    // Ps == Qs + ([p] + tail), use distinct_append
    assert Ps == Qs + ([p] + tail);
    distinct_append(Qs, [p] + tail);
    assert p in [p] + tail;
    assert p !in Qs;
    distinct_prefix(Qs, tail, p);
    assert distinct(Qs + [p]);

    // Split the path Ps at Qs to get path from p through [p] + tail to 0
    path_split(next, free_list, 0, Qs, [p] + tail);
    ghost var z :| path(next, free_list, Qs, z) && path(next, z, [p] + tail, 0);
    // z == p from path_function (both Qs-paths end at p)
    path_function(next, free_list, z, p, Qs);
    assert z == p;
    assert path(next, p, [p] + tail, 0);
    // This gives us: p != 0, p == p, p in next, path(next, next[p], tail, 0)

    Qs := Qs + [p];
    q := p;
    p := next[p];

    // Establish p in next for the new p
    // next[old_p] == tail[0] if tail non-empty, else next[old_p] == 0
    if |tail| > 0 {
      assert next[old_p] == tail[0];
      assert tail[0] in Ps;
      assert p in next;
    } else {
      assert next[old_p] == 0;
      assert p == 0;
    }

    // q (= old_p) is in the domain
    assert q in next;

    // Witness for exists Qs' :: distPath(next, free_list, Qs', q)
    assert distPath(next, free_list, old_Qs, q);
  }

  if p != 0 {
    // Found a suitable block at p
    // From loop exit: block_size(p) >= size
    assert block_size(p) >= size;

    // Ps == Qs + [p] + Rest for some Rest
    path_prefix_of_path_to_zero(next, free_list, p, Qs, Ps);
    ghost var Rest :| Ps == Qs + [p] + Rest;

    // FindFirst(Ps, block_size, size) == Some(p)
    find_in_split(Qs, Rest, p, block_size, size);
    assert FindFirst(Ps, block_size, size) == Some(p);

    // Unlink p: next' = next[q := next[p]]
    assert p in next;
    ghost var next_before := next;
    next := next[q := next[p]];
    mem := p;

    // Erase(Ps, p) == Qs + Rest (since Ps is distinct)
    erase_middle_unique(Qs, Rest, p);
    assert Erase(Ps, p) == Qs + Rest;

    // distPath(next[q := next[p]], free_list, Qs + Rest, 0)
    // Use path_update_skip: skip p in the path Qs ++ [q] ++ [p] ++ Rest
    // But wait: q is the last element of Qs, so Qs = Qs_init ++ [q]
    ghost var Qs_init := Qs[..|Qs| - 1];
    assert Qs == Qs_init + [q];

    // Ps == Qs_init + [q] + [p] + Rest
    assert Ps == Qs_init + [q] + [p] + Rest;

    // Apply path_update_skip
    path_update_skip(next_before, free_list, Qs_init, q, p, Rest);
    // Gives: path(next_before[q := next_before[p]], free_list, Qs_init + [q] + Rest, 0)
    assert path(next, free_list, Qs_init + [q] + Rest, 0);
    assert Qs_init + [q] + Rest == Qs + Rest;

    // Distinct: Qs + Rest is a sublist of Ps which is distinct
    distinct_append(Qs + [p], Rest);
    distinct_append(Qs, [p] + Rest);
    distinct_append(Qs, Rest);

    return;
  } else {
    // No suitable block found
    mem := 0;

    // All blocks in Qs are too small, and Qs covers all of Ps
    // (since p == 0, the path from free_list through Qs reaches 0)
    assert p == 0;
    assert distPath(next, free_list, Qs, 0);
    path_zero_unique(next, free_list, Qs, Ps);
    assert Qs == Ps;

    // So all blocks in Ps are too small
    assert forall a :: a in Ps ==> block_size(a) < size;
    find_none_if_all_fail(Ps, block_size, size);
    assert FindFirst(Ps, block_size, size) == None;
    // Postcondition is vacuously true
    return;
  }
}
