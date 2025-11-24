import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"
set_option loom.solver "cvc5"
set_option loom.solver.smt.timeout 5

--this will ne our answer type
structure SubstringResult where
  l : Nat
  r : Nat
  flag: Bool
deriving Repr, Inhabited

--predicate for substring all characters of which satisfy the predicate
@[loomAbstractionSimp]
def CorrectSubstring (s : Array Char) (p : Char -> Bool) (l r : Nat) : Prop :=
  l ≤ r ∧ r < s.size ∧
  (∀ i, l ≤ i ∧ i ≤ r → p s[i]!)

--actual method
--  if there are no substrings,
--  flag is false and all characters do not satisfy the predicate
method SubstringSearch (s: Array Char) (p: Char -> Bool) return (res: SubstringResult)
--postconditions, don't need any preconditions.
ensures (res.l ≤ res.r)
ensures 0 < s.size → res.r < s.size
ensures res.flag → CorrectSubstring s p res.l res.r
ensures res.flag →
  (∀ l₁ r₁, CorrectSubstring s p l₁ r₁ →
    r₁ - l₁ + 1 = res.r - res.l + 1 ∧ res.r ≤ r₁ ∨
    r₁ - l₁ + 1 < res.r - res.l + 1)
ensures ¬res.flag → ∀ i < s.size, ¬p s[i]!
do
    if s.size = 0 then
      --basic case with an empty string
      return ⟨0, 0, false⟩
    let mut cnt := 0
    let mut pnt := 0
    let mut ans := 0
    let mut l_ans := 0
    let mut r_ans := 0
    while pnt < s.size
    --loop invariants
    invariant 0 ≤ cnt
    invariant cnt ≤ pnt
    invariant pnt ≤ s.size
    invariant l_ans ≤ r_ans
    invariant r_ans < s.size
    invariant cnt ≤ ans
    invariant r_ans ≤ pnt
    invariant ∀ j, pnt - cnt ≤ j ∧ j < pnt → p s[j]!
    invariant ans > 0 →
        ans = r_ans - l_ans + 1 ∧
        CorrectSubstring s p l_ans r_ans
    invariant ans = 0 → (∀ i, i < pnt → ¬p s[i]!)
    invariant cnt < pnt → ¬p s[pnt - cnt - 1]!
    invariant ∀ l₁ r₁,
        CorrectSubstring s p l₁ r₁ ∧ r₁ < pnt →
        r₁ - l₁ + 1 = ans ∧ r_ans ≤ r₁ ∨ r₁ - l₁ + 1 < ans
    --value decreases by 1 with each iteration,
    --therefore time complexity is O(size s), as other parts
    --take constant time
    decreasing s.size - pnt
    do
      --loop body
      if p s[pnt]! then
        cnt := cnt + 1
        if ans < cnt then
          l_ans := pnt + 1 - cnt
          r_ans := pnt
          ans := cnt
      else
        cnt := 0
      pnt := pnt + 1
    return ⟨l_ans, r_ans, ans > 0⟩

prove_correct SubstringSearch by
  loom_solve

--prove theorem not about the monadic computation but the actual
--extract result
theorem finalCorrectnessTheorem (s : Array Char) (p : Char → Bool) :
  let res := SubstringSearch s p |>.extract
  (res.flag = false → ∀ i < s.size, p s[i]! = false) ∧
  (res.flag = true →
    (∀ l₁ r₁, CorrectSubstring s p l₁ r₁ →
  r₁ - l₁ + 1 = res.r - res.l + 1 ∧ res.r ≤ r₁ ∨
  r₁ - l₁ + 1 < res.r - res.l + 1)) ∧
  (res.flag = true → CorrectSubstring s p res.l res.r) ∧
  (0 < s.size → res.r < s.size) ∧
  (res.l ≤ res.r) := by
    grind [VelvetM.extract_spec, SubstringSearch_correct]
