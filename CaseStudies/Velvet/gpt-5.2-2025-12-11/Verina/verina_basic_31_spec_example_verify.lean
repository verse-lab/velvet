import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000

def precondition (s : String) : Prop :=
  True

def postcondition (s : String) (result : String) : Prop :=
  result.length = s.length ∧
    (∀ (i : Nat), i < s.length → result.toList[i]! = (s.toList[i]!).toUpper)


def test1_s : String := "Hello, World!"

def test1_Expected : String := "HELLO, WORLD!"

def test2_s : String := "abc"

def test2_Expected : String := "ABC"

def test5_s : String := ""

def test5_Expected : String := ""







section Proof
theorem test1_precondition :
  precondition test1_s := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_s test1_Expected := by
  unfold postcondition test1_s test1_Expected
  native_decide

theorem test2_precondition :
  precondition test2_s := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_s test2_Expected := by
  -- unfold concrete definitions
  simp [postcondition, test2_s, test2_Expected]
  constructor
  · decide
  · intro i hi
    -- `simp` already reduced `s.length` to `3`, so we case split on `i < 3`.
    have hi' : i < 3 := hi
    have h0 : i = 0 ∨ i = 1 ∨ i = 2 := by
      omega
    rcases h0 with rfl | rfl | rfl
    · decide
    · decide
    · decide

theorem test5_precondition :
  precondition test5_s := by
  intros; expose_names; exact (trivial); done

theorem test5_postcondition :
  postcondition test5_s test5_Expected := by
  simp [postcondition, test5_s, test5_Expected]

theorem uniqueness_0
    (s : String)
    (hsPre : precondition s)
    (ret1 : String)
    (ret2 : String)
    (hPost1 : postcondition s ret1)
    (hPost2 : postcondition s ret2)
    (hPreTriv : True)
    (hLen1 : ret1.length = s.length)
    (hLen2 : ret2.length = s.length)
    (hLen12 : ret1.length = ret2.length)
    (hBound1 : ∀ i < s.length, i < ret1.length)
    (hBound2 : ∀ i < s.length, i < ret2.length)
    (i : ℕ)
    (hi1 : i < ret1.toList.length)
    (hi2 : i < ret2.toList.length)
    (hChar1 : ∀ i < s.length, ret1.data[i]?.getD 'A' = (s.data[i]?.getD 'A').toUpper)
    (hChar2 : ∀ i < s.length, ret2.data[i]?.getD 'A' = (s.data[i]?.getD 'A').toUpper)
    (hGetBangEq_s : ∀ i < s.length, ret1.data[i]?.getD 'A' = ret2.data[i]?.getD 'A')
    : ret1.data[i] = ret2.data[i] := by
    -- Convert the bounds on toList into bounds on data
    have hi1' : i < ret1.data.length := by
      simpa [String.toList] using hi1
    have hi2' : i < ret2.data.length := by
      simpa [String.toList] using hi2

    -- From i < ret1.length and ret1.length = s.length, get i < s.length
    have hiS : i < s.length := by
      -- ret1.length is definitionally ret1.data.length
      have : i < ret1.length := by
        simpa [String.length] using hi1'
      simpa [hLen1] using this

    -- Use the provided pointwise equality (with getD) at index i
    have hEqGetD : ret1.data[i]?.getD 'A' = ret2.data[i]?.getD 'A' :=
      hGetBangEq_s i hiS

    -- When i is in bounds, get? i = some (l[i]) and getD returns that element
    have hSome1 : ret1.data.get? i = some (ret1.data[i]'hi1') := by
      simpa using (List.get?_eq_get (l := ret1.data) hi1')
    have hSome2 : ret2.data.get? i = some (ret2.data[i]'hi2') := by
      simpa using (List.get?_eq_get (l := ret2.data) hi2')

    have hGetD1 : ret1.data[i]?.getD 'A' = (ret1.data[i]'hi1') := by
      -- unfold get? notation and rewrite by hSome1
      simpa [List.get?, hSome1] using (congrArg (fun x => Option.getD x 'A') hSome1)
    have hGetD2 : ret2.data[i]?.getD 'A' = (ret2.data[i]'hi2') := by
      simpa [List.get?, hSome2] using (congrArg (fun x => Option.getD x 'A') hSome2)

    have hEqGet : (ret1.data[i]'hi1') = (ret2.data[i]'hi2') := by
      -- rewrite hEqGetD using the identifications of getD with actual elements
      calc
        (ret1.data[i]'hi1')
            = ret1.data[i]?.getD 'A' := by simpa [hGetD1]
        _   = ret2.data[i]?.getD 'A' := hEqGetD
        _   = (ret2.data[i]'hi2') := by simpa [hGetD2]

    -- The goal uses the GetElem instance; this is definitional to the same get with proof hi1'/hi2'
    simpa using hEqGet

theorem uniqueness (s : String):
  precondition s →
  (∀ ret1 ret2,
    postcondition s ret1 →
    postcondition s ret2 →
    ret1 = ret2) := by
  intro hsPre
  intro ret1 ret2 hPost1 hPost2

  -- Step 2: precondition is irrelevant (it is definitionaly True)
  have hPreTriv : True := by
    simpa [precondition] using hsPre

  -- Step 3: unpack postcondition for ret1
  have hLen1 : ret1.length = s.length := by
    simpa [postcondition] using hPost1.1
  have hChar1 : ∀ (i : Nat), i < s.length → ret1.toList[i]! = (s.toList[i]!).toUpper := by
    simpa [postcondition] using hPost1.2

  -- Step 4: unpack postcondition for ret2
  have hLen2 : ret2.length = s.length := by
    simpa [postcondition] using hPost2.1
  have hChar2 : ∀ (i : Nat), i < s.length → ret2.toList[i]! = (s.toList[i]!).toUpper := by
    simpa [postcondition] using hPost2.2

  -- Step 5: same length for ret1 and ret2
  have hLen12 : ret1.length = ret2.length := by
    -- ret1.length = s.length = ret2.length
    calc
      ret1.length = s.length := by simpa using hLen1
      _ = ret2.length := by simpa using hLen2.symm

  -- Step 7 (part): rewrite bounds i < s.length into i < ret1.length / i < ret2.length
  have hBound1 : ∀ i : Nat, i < s.length → i < ret1.length := by
    intro i hi
    simpa [hLen1] using hi
  have hBound2 : ∀ i : Nat, i < s.length → i < ret2.length := by
    intro i hi
    simpa [hLen2] using hi

  -- Step 6: pointwise equality of characters at each valid index (stated with bound i < s.length)
  have hGetBangEq_s : ∀ (i : Nat), i < s.length → ret1.toList[i]! = ret2.toList[i]! := by
    intro i hi
    have h1i : ret1.toList[i]! = (s.toList[i]!).toUpper := by
      exact hChar1 i hi
    have h2i : ret2.toList[i]! = (s.toList[i]!).toUpper := by
      exact hChar2 i hi
    -- rewrite both sides to the same middle expression
    calc
      ret1.toList[i]! = (s.toList[i]!).toUpper := by simpa using h1i
      _ = ret2.toList[i]! := by simpa using h2i.symm

  -- Step 8: equality of toList using List.ext_getElem (convert get! to bounded getElem)
  have hToListEq : ret1.toList = ret2.toList := by
    apply List.ext_getElem
    · -- lengths of lists are equal
      -- (ret1.toList).length = ret1.length and similarly for ret2; then use hLen12
      -- (String.length is definitionally List.length of toList, but we keep it as a subproof)
      simpa using congrArg (fun t => t) hLen12
    · intro i hi1 hi2
      -- reduce to the get! equalities at index i under the corresponding bounds
      -- and use hGetBangEq_s together with rewriting bounds via hLen1/hLen2.
      -- (Details about getElem vs get! are left to simp/lemmas.)
      (try simp at *; expose_names); exact (uniqueness_0 s hsPre ret1 ret2 hPost1 hPost2 hPreTriv hLen1 hLen2 hLen12 hBound1 hBound2 i hi1 hi2 hChar1 hChar2 hGetBangEq_s); done

  -- Step 9: convert equality of toList to equality of strings
  have hStrEq : ret1 = ret2 := by
    -- use extensionality / injectivity of toList
    -- e.g. `exact String.ext (by simpa [hToListEq])` or `exact congrArg String.ofList hToListEq` + simp
    (try simp at *; expose_names); exact String.ext hToListEq; done

  -- Step 10: finish
  exact hStrEq
end Proof
