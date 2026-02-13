import Velvet.Std

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

method test1 (n : Nat) return (res : Nat)
  ensures n = res
  do
    match n with
    | .zero => pure 0
    | .succ k =>
      let b ← test1 k
      pure (Nat.succ b)
-- set_option trace.Loom.debug true in
prove_correct test1 by
  loom_solve


/-
-- FIXME: error in the "compilation"
method test1' (n : Nat) return (res : Nat)
  ensures n = res
  do
    let res ← match n with
      | .zero => pure 0
      | .succ k =>
        let b ← test1' k
        pure (Nat.succ b)
    pure res
-/

method test2 (n : β) (l : List α) return (res : Nat)
  ensures res = l.length
  do
    match l, n with
    | [], _ => pure 0
    | _ :: k, _ =>
      let b ← test2 n k
      pure b.succ
-- set_option trace.Loom.debug true in
prove_correct test2
decreasing_by
  all_goals (simp_all ; grind) by
  unfold test2
  loom_solve

method test3 (a : Nat) (b : Nat) (c : Nat) return (res : Nat)
  ensures res > 9
  do
    match a, b, c with
    | 2, 3, 4 => pure (10 : Nat)
    | _, _, _ => pure (a + b + c + 10)
prove_correct test3 by
  loom_solve
