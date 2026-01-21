import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def replChar (oldChar : Char) (newChar : Char) (c : Char) : Char :=
  if c = oldChar then newChar else c



def precondition (s : String) (oldChar : Char) (newChar : Char) : Prop :=
  True




def postcondition (s : String) (oldChar : Char) (newChar : Char) (result : String) : Prop :=
  result.toList.length = s.toList.length ∧
  (∀ (i : Nat), i < s.toList.length →
    result.toList[i]! = replChar oldChar newChar (s.toList[i]!))


def test1_s : String := "hello, world!"

def test1_oldChar : Char := ','

def test1_newChar : Char := ';'

def test1_Expected : String := "hello; world!"

def test3_s : String := "hello, world!"

def test3_oldChar : Char := 'o'

def test3_newChar : Char := 'O'

def test3_Expected : String := "hellO, wOrld!"

def test7_s : String := "aaa"

def test7_oldChar : Char := 'a'

def test7_newChar : Char := 'b'

def test7_Expected : String := "bbb"







section Proof
theorem test1_precondition :
  precondition test1_s test1_oldChar test1_newChar := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_s test1_oldChar test1_newChar test1_Expected := by
  unfold postcondition
  constructor
  · simp [test1_s, test1_Expected]
  · intro i hi
    -- compute the concrete list forms and then do bounded case split on `i`
    have hi' : i < 13 := by
      simpa [test1_s] using hi
    interval_cases i <;>
      simp [test1_s, test1_Expected, replChar, test1_oldChar, test1_newChar]

theorem test3_precondition :
  precondition test3_s test3_oldChar test3_newChar := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_s test3_oldChar test3_newChar test3_Expected := by
  unfold postcondition
  constructor
  · simp [test3_s, test3_Expected]
  · intro i hi
    -- reduce the bound to the concrete length of the literal string
    have hi' : i < 13 := by
      simpa [test3_s] using hi
    -- split into all possible indices and compute
    interval_cases i <;> simp [test3_s, test3_oldChar, test3_newChar, test3_Expected, replChar]

theorem test7_precondition :
  precondition test7_s test7_oldChar test7_newChar := by
  intros; expose_names; exact (trivial); done

theorem test7_postcondition :
  postcondition test7_s test7_oldChar test7_newChar test7_Expected := by
  unfold postcondition
  constructor
  · simp [test7_s, test7_Expected]
  · intro i hi
    have hi' : i < 3 := by
      simpa [test7_s] using hi
    have h0 : i = 0 ∨ i = 1 ∨ i = 2 := by
      omega
    rcases h0 with rfl | rfl | rfl <;>
      simp [test7_s, test7_Expected, replChar, test7_oldChar, test7_newChar]

theorem uniqueness_0
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (hpre : precondition s oldChar newChar)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition s oldChar newChar ret1)
    (hpost2 : postcondition s oldChar newChar ret2)
    (hpost1_len : ret1.data.length = s.data.length)
    (hpost2_len : ret2.data.length = s.data.length)
    (hlen : ret1.data.length = ret2.data.length)
    (n : ℕ)
    (hn : n < s.data.length)
    (hpost1_spec : ∀ i < s.data.length, ret1.data[i]?.getD 'A' = replChar oldChar newChar (s.data[i]?.getD 'A'))
    (hpost2_spec : ∀ i < s.data.length, ret2.data[i]?.getD 'A' = replChar oldChar newChar (s.data[i]?.getD 'A'))
    (hpoint : ∀ i < s.data.length, ret1.data[i]?.getD 'A' = ret2.data[i]?.getD 'A')
    (hgn : ret1.data[n]?.getD 'A' = ret2.data[n]?.getD 'A')
    : ret1.data[n]? = ret2.data[n]? := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_1
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (hpre : precondition s oldChar newChar)
    (ret1 : String)
    (ret2 : String)
    (hpost1 : postcondition s oldChar newChar ret1)
    (hpost2 : postcondition s oldChar newChar ret2)
    (hpost1_len : ret1.data.length = s.data.length)
    (hpost2_len : ret2.data.length = s.data.length)
    (hlen : ret1.data.length = ret2.data.length)
    (n : ℕ)
    (hpost1_spec : ∀ i < s.data.length, ret1.data[i]?.getD 'A' = replChar oldChar newChar (s.data[i]?.getD 'A'))
    (hpost2_spec : ∀ i < s.data.length, ret2.data[i]?.getD 'A' = replChar oldChar newChar (s.data[i]?.getD 'A'))
    (hpoint : ∀ i < s.data.length, ret1.data[i]?.getD 'A' = ret2.data[i]?.getD 'A')
    (hn : s.data.length ≤ n)
    (hn1 : ret1.data.length ≤ n)
    (hn2 : ret2.data.length ≤ n)
    : ret1.data[n]? = ret2.data[n]? := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness (s : String) (oldChar : Char) (newChar : Char):
  precondition s oldChar newChar →
  (∀ ret1 ret2,
    postcondition s oldChar newChar ret1 →
    postcondition s oldChar newChar ret2 →
    ret1 = ret2) := by
  intro hpre
  intro ret1 ret2 hpost1 hpost2

  -- extract the two components of each postcondition
  have hpost1_len : ret1.toList.length = s.toList.length := by
    simpa [postcondition] using hpost1.1
  have hpost1_spec :
      ∀ i : Nat, i < s.toList.length →
        ret1.toList[i]! = replChar oldChar newChar (s.toList[i]!) := by
    simpa [postcondition] using hpost1.2
  have hpost2_len : ret2.toList.length = s.toList.length := by
    simpa [postcondition] using hpost2.1
  have hpost2_spec :
      ∀ i : Nat, i < s.toList.length →
        ret2.toList[i]! = replChar oldChar newChar (s.toList[i]!) := by
    simpa [postcondition] using hpost2.2

  -- derive equal lengths of the two result lists
  have hlen : ret1.toList.length = ret2.toList.length := by
    calc
      ret1.toList.length = s.toList.length := by simpa using hpost1_len
      _ = ret2.toList.length := by simpa using hpost2_len.symm

  -- pointwise equality of get! for indices valid in s
  have hpoint : ∀ i : Nat, i < s.toList.length → ret1.toList[i]! = ret2.toList[i]! := by
    intro i hi
    have h1i : ret1.toList[i]! = replChar oldChar newChar (s.toList[i]!) := by
      exact hpost1_spec i hi
    have h2i : ret2.toList[i]! = replChar oldChar newChar (s.toList[i]!) := by
      exact hpost2_spec i hi
    have h2i' : replChar oldChar newChar (s.toList[i]!) = ret2.toList[i]! := by
      exact Eq.symm h2i
    exact Eq.trans h1i h2i'

  -- convert pointwise get! equality (in range) into pointwise get? equality (all n)
  have hget? : ∀ n : Nat, ret1.toList.get? n = ret2.toList.get? n := by
    intro n
    by_cases hn : n < s.toList.length
    · have hgn : ret1.toList[n]! = ret2.toList[n]! := by
        exact hpoint n hn
      -- turn get! equality into get? equality at an in-bounds index
      -- (e.g. via `List.get?_eq_get` plus relating `get!` to the corresponding `get`)
      (try simp at *; expose_names); exact (uniqueness_0 s oldChar newChar hpre ret1 ret2 hpost1 hpost2 hpost1_len hpost2_len hlen n hn hpost1_spec hpost2_spec hpoint hgn); done
    · -- out of bounds for s; use the length equalities to show both get? are none
      have hn1 : ¬ n < ret1.toList.length := by
        -- rewrite ret1 length to s length, then use hn
        -- (use `hpost1_len` to rewrite; avoiding the previous attempt's simp mismatch)
        (try simp at *; expose_names); exact le_of_eq_of_le hpost1_len hn; done
      have hn2 : ¬ n < ret2.toList.length := by
        -- rewrite ret2 length to s length, then use hn
        (try simp at *; expose_names); exact le_of_eq_of_le hpost2_len hn; done
      -- conclude both sides are none
      (try simp at *; expose_names); exact (uniqueness_1 s oldChar newChar hpre ret1 ret2 hpost1 hpost2 hpost1_len hpost2_len hlen n hpost1_spec hpost2_spec hpoint hn hn1 hn2); done

  -- list equality from equality of get? at all indices
  have hlist : ret1.toList = ret2.toList := by
    exact List.ext_get? hget?

  -- string equality from toList equality
  have hstr : ret1 = ret2 := by
    -- `String.ext` expects equality of `.data` (aka `.toList`)
    exact String.ext hlist

  exact hstr
end Proof
