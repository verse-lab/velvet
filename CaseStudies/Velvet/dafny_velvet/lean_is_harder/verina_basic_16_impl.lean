import CaseStudies.Velvet.Std
import Mathlib.Data.String.Basic

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    replaceChars: Replace every occurrence of a specified character in a string.
    Natural language breakdown:
    1. Inputs are a string s and two characters oldChar and newChar.
    2. The result is a string with the same number of characters as s.
    3. For each index i within bounds, if the i-th character of s equals oldChar,
       then the i-th character of the result equals newChar.
    4. For each index i within bounds, if the i-th character of s does not equal oldChar,
       then the i-th character of the result equals the i-th character of s.
    5. There are no preconditions; the method must work for any string and characters.
-/

section Specs
-- Helper: pointwise replacement on characters.
-- This is a simple, computable predicate used in the postcondition.
def replChar (oldChar : Char) (newChar : Char) (c : Char) : Char :=
  if c = oldChar then newChar else c

-- No preconditions.
def precondition (s : String) (oldChar : Char) (newChar : Char) : Prop :=
  True

-- Postcondition: list-view length preserved and pointwise replacement behavior on `toList`.
-- We specify everything through `toList` to avoid mixing different views (`String.length` vs list length).
def postcondition (s : String) (oldChar : Char) (newChar : Char) (result : String) : Prop :=
  result.toList.length = s.toList.length ∧
  (∀ (i : Nat), i < s.toList.length →
    result.toList[i]! = replChar oldChar newChar (s.toList[i]!))
end Specs

section Impl
method replaceChars (s : String) (oldChar : Char) (newChar : Char)
  return (result : String)
  require precondition s oldChar newChar
  ensures postcondition s oldChar newChar result
  do
  let chars := s.toList
  let mut out := ""
  let mut i : Nat := 0
  while i < chars.length
    -- i stays within bounds of `chars`.
    -- Init: i = 0. Preserved: i increases by 1 while guard enforces i < chars.length.
    invariant "inv_bounds" i ≤ chars.length
    -- `out` is the result of pointwise replacement on the prefix processed so far.
    -- Init: i=0, out="". Preserved: we append exactly replChar(...) of chars[i]!
    -- Suffices: at exit i=chars.length, we have full list processed.
    invariant "inv_out_list" out.toList = (List.map (replChar oldChar newChar) (chars.take i))
  do
    let c := chars[i]!
    let c' := replChar oldChar newChar c
    out := out.push c'
    i := i + 1
  return out
end Impl

section Proof
set_option maxHeartbeats 10000000

-- prove_correct replaceChars by
  -- loom_solve <;> (try simp at *; expose_names)

theorem goal_0_0
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (if_pos : i < s.length)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    (h_i_lt_dataLen : i < s.data.length)
    (h_i_lt_mapLen : i < s.length)
    : s.data[i]?.getD 'A' = s.data[i] := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_0
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (if_pos : i < s.length)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    : out.data ++ [replChar oldChar newChar (s.data[i]?.getD 'A')] = List.take (i + 1) (List.map (replChar oldChar newChar) s.data) := by
  -- Step 1: convert the loop guard `i < s.length` into `i < s.data.length`
  have h_i_lt_dataLen : i < s.data.length := by
    -- avoid `simp [String.length]` recursion; use the constructor `s = ⟨s.data⟩`
    cases s with
    | mk cs =>
      -- goal becomes `i < cs.length` and `if_pos` becomes `i < (String.mk cs).length`
      simpa [String.length] using if_pos

  -- Step 2: lift the bound through `map` (length of map is length)
  have h_i_lt_mapLen : i < (List.map (replChar oldChar newChar) s.data).length := by
    -- `List.length_map` (simp) turns this into `i < s.data.length`
    simpa using (show i < s.data.length from h_i_lt_dataLen)

  -- Step 3: since `i` is in bounds, `getD` returns the real element (default irrelevant)
  have h_getD_eq_getElem : s.data[i]?.getD 'A' = s.data[i] := by
    -- prove by rewriting `get?` to `some` using the bound, then `Option.getD`
    (try simp at *; expose_names); exact (goal_0_0 s oldChar newChar require_1 i out invariant_inv_bounds if_pos invariant_inv_out_list h_i_lt_dataLen h_i_lt_mapLen); done

  -- Step 4: rewrite the appended character using Step 3
  have h_repl_getD :
      replChar oldChar newChar (s.data[i]?.getD 'A') =
        replChar oldChar newChar (s.data[i]) := by
    -- congruence
    (try simp at *; expose_names); exact congrArg (replChar oldChar newChar) h_getD_eq_getElem; done

  -- Step 5: decompose `take (i+1)` on the mapped list
  have h_take_succ_mapped :
      List.take (i + 1) (List.map (replChar oldChar newChar) s.data) =
        List.take i (List.map (replChar oldChar newChar) s.data) ++
          [(List.map (replChar oldChar newChar) s.data)[i]] := by
    -- `List.take_succ_eq_append_getElem` gives exactly this shape
    simpa using
      (List.take_succ_eq_append_getElem
        (l := List.map (replChar oldChar newChar) s.data) (i := i) h_i_lt_mapLen)

  -- Step 6: compute the `i`th element of the mapped list as mapping the `i`th element
  have h_map_getElem :
      (List.map (replChar oldChar newChar) s.data)[i] =
        replChar oldChar newChar (s.data[i]) := by
    -- standard `getElem_map`-style lemma
    (try simp at *; expose_names); exact List.getElem_map (replChar oldChar newChar); done

  -- Step 7: specialize Step 5 using Step 6 to express RHS as `take i ++ [f (s[i])]`
  have h_rhs_as_append :
      List.take (i + 1) (List.map (replChar oldChar newChar) s.data) =
        List.take i (List.map (replChar oldChar newChar) s.data) ++
          [replChar oldChar newChar (s.data[i])] := by
    -- rewrite the singleton element in Step 5 via Step 6
    (try simp at *; expose_names); exact h_take_succ_mapped; done

  -- Step 8: rewrite `out.data` by invariant, then match both sides via Step 7 and Step 4
  calc
    out.data ++ [replChar oldChar newChar (s.data[i]?.getD 'A')]
        =
      (List.take i (List.map (replChar oldChar newChar) s.data)) ++
        [replChar oldChar newChar (s.data[i]?.getD 'A')] := by
          simpa [invariant_inv_out_list]
    _   =
      (List.take i (List.map (replChar oldChar newChar) s.data)) ++
        [replChar oldChar newChar (s.data[i])] := by
          simpa [h_repl_getD]
    _   =
      List.take (i + 1) (List.map (replChar oldChar newChar) s.data) := by
          -- use Step 7 in reverse
          simpa [h_rhs_as_append]

theorem goal_1
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    : "".toList = List.map (replChar oldChar newChar) (List.take 0 s.toList) := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_0
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (i_1 : ℕ)
    (out_1 : String)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    (done_1 : s.length ≤ i)
    (i_2 : i = i_1 ∧ out = out_1)
    : out = out_1 := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_1
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (i_1 : ℕ)
    (out_1 : String)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    (done_1 : s.length ≤ i)
    (i_2 : i = i_1 ∧ out = out_1)
    (h_out_eq_out1 : out = out_1)
    (h_i_eq_len : i = s.length)
    (h_len_le_i_map : s.length ≤ i)
    (h_take_i_map_eq_map : s.length ≤ i)
    : out.data = List.map (replChar oldChar newChar) s.data := by
  -- rewrite the invariant at loop exit to a take at `s.length`
  have hout : out.data = List.take s.length (List.map (replChar oldChar newChar) s.data) := by
    simpa [h_i_eq_len] using invariant_inv_out_list
  -- `take` of the full length is the list itself
  have htake :
      List.take s.length (List.map (replChar oldChar newChar) s.data) =
        List.map (replChar oldChar newChar) s.data := by
    -- use the fact that `s.length = s.data.length` (by cases on `s`)
    cases s with
    | mk cs =>
      simp [String.length_mk]
  -- finish
  simpa [htake] using hout

theorem goal_2_2
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (i_1 : ℕ)
    (out_1 : String)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    (done_1 : s.length ≤ i)
    (i_2 : i = i_1 ∧ out = out_1)
    (h_out_eq_out1 : out = out_1)
    (h_i_eq_len : i = s.length)
    (h_out_data_eq_map : out.data = List.map (replChar oldChar newChar) s.data)
    (h_out_toList_eq_map : out.data = List.map (replChar oldChar newChar) s.data)
    (h_len_le_i_map : s.length ≤ i)
    (h_take_i_map_eq_map : s.length ≤ i)
    : out.length = s.length := by
    -- reduce to list lengths via `String.length_mk`
    cases s with
    | mk sdata =>
      cases out with
      | mk outdata =>
        -- use the given equality on `.data` and `List.length_map`
        have h' : outdata = List.map (replChar oldChar newChar) sdata := by
          simpa using h_out_data_eq_map
        -- now finish by taking lengths
        simpa [String.length_mk, h', List.length_map]

theorem goal_2_3
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (i_1 : ℕ)
    (out_1 : String)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    (done_1 : s.length ≤ i)
    (i_2 : i = i_1 ∧ out = out_1)
    (h_out_eq_out1 : out = out_1)
    (h_i_eq_len : i = s.length)
    (h_out_data_eq_map : out.data = List.map (replChar oldChar newChar) s.data)
    (h_out_toList_eq_map : out.data = List.map (replChar oldChar newChar) s.data)
    (h_len_part_out : out.length = s.length)
    (i0 : ℕ)
    (hi0 : i0 < s.toList.length)
    (h_i0_lt_mapLen : i0 < (List.map (replChar oldChar newChar) s.toList).length)
    (h_len_le_i_map : s.length ≤ i)
    (h_take_i_map_eq_map : s.length ≤ i)
    (h_get_map : True)
    : out.data[i0]?.getD 'A' = (Option.map (replChar oldChar newChar) s.data[i0]?).getD 'A' := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem goal_2_4
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (i_1 : ℕ)
    (out_1 : String)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    (done_1 : s.length ≤ i)
    (i_2 : i = i_1 ∧ out = out_1)
    (h_out_eq_out1 : out = out_1)
    (h_i_eq_len : i = s.length)
    (h_out_data_eq_map : out.data = List.map (replChar oldChar newChar) s.data)
    (h_out_toList_eq_map : out.data = List.map (replChar oldChar newChar) s.data)
    (h_len_part_out : out.length = s.length)
    (i0 : ℕ)
    (hi0 : i0 < s.toList.length)
    (h_i0_lt_mapLen : i0 < (List.map (replChar oldChar newChar) s.toList).length)
    (h_len_le_i_map : s.length ≤ i)
    (h_take_i_map_eq_map : s.length ≤ i)
    (h_get_map : True)
    (h_out_get_eq : out.data[i0]?.getD 'A' = (Option.map (replChar oldChar newChar) s.data[i0]?).getD 'A')
    : (Option.map (replChar oldChar newChar) s.data[i0]?).getD 'A' = replChar oldChar newChar (s.data[i0]?.getD 'A') := by
    -- show the index is in bounds for `s.data`
    have hi0' : i0 < s.data.length := by
      simpa [String.toList] using hi0

    -- rewrite the optional lookup at an in-bounds index to `some _`
    have hs : s.data[i0]? = some s.data[i0] := by
      simpa using (List.getElem?_eq_getElem (l := s.data) (i := i0) hi0')

    -- now both sides reduce to the same expression
    simp [hs]

theorem goal_2
    (s : String)
    (oldChar : Char)
    (newChar : Char)
    (require_1 : precondition s oldChar newChar)
    (i : ℕ)
    (out : String)
    (invariant_inv_bounds : i ≤ s.length)
    (i_1 : ℕ)
    (out_1 : String)
    (invariant_inv_out_list : out.data = List.take i (List.map (replChar oldChar newChar) s.data))
    (done_1 : s.length ≤ i)
    (i_2 : i = i_1 ∧ out = out_1)
    : postcondition s oldChar newChar out_1 := by
  have h_out_eq_out1 : out = out_1 := by (try simp at *; expose_names); exact (goal_2_0 s oldChar newChar require_1 i out invariant_inv_bounds i_1 out_1 invariant_inv_out_list done_1 i_2); done
  have h_i_eq_len : i = s.length := by (try simp at *; expose_names); exact (Nat.le_antisymm invariant_inv_bounds done_1); done
  have h_len_le_i_map : (List.map (replChar oldChar newChar) s.data).length ≤ i := by (try simp at *; expose_names); exact (done_1); done
  have h_take_i_map_eq_map : List.take i (List.map (replChar oldChar newChar) s.data) = List.map (replChar oldChar newChar) s.data := by (try simp at *; expose_names); exact (done_1); done
  have h_out_data_eq_map : out.data = List.map (replChar oldChar newChar) s.data := by (try simp at *; expose_names); exact (goal_2_1 s oldChar newChar require_1 i out invariant_inv_bounds i_1 out_1 invariant_inv_out_list done_1 i_2 h_out_eq_out1 h_i_eq_len h_len_le_i_map h_take_i_map_eq_map); done
  have h_out_toList_eq_map : out.toList = List.map (replChar oldChar newChar) s.toList := by (try simp at *; expose_names); exact (h_out_data_eq_map); done
  have h_len_part_out : out.toList.length = s.toList.length := by (try simp at *; expose_names); exact (goal_2_2 s oldChar newChar require_1 i out invariant_inv_bounds i_1 out_1 invariant_inv_out_list done_1 i_2 h_out_eq_out1 h_i_eq_len h_out_data_eq_map h_out_toList_eq_map h_len_le_i_map h_take_i_map_eq_map); done
  have h_pointwise_part_out : ∀ (i0 : Nat), i0 < s.toList.length → out.toList[i0]! = replChar oldChar newChar (s.toList[i0]!) := by
    intro i0 hi0
    have h_i0_lt_mapLen : i0 < (List.map (replChar oldChar newChar) s.toList).length := by (try simp at *; expose_names); exact (hi0); done
    have h_get_map : (List.map (replChar oldChar newChar) s.toList)[i0] = replChar oldChar newChar (s.toList[i0]'(by simpa using hi0)) := by (try simp at *; expose_names); exact (List.getElem_map (replChar oldChar newChar)); done
    have h_out_get_eq : out.toList[i0]! = (List.map (replChar oldChar newChar) s.toList)[i0]! := by (try simp at *; expose_names); exact (goal_2_3 s oldChar newChar require_1 i out invariant_inv_bounds i_1 out_1 invariant_inv_out_list done_1 i_2 h_out_eq_out1 h_i_eq_len h_out_data_eq_map h_out_toList_eq_map h_len_part_out i0 hi0 h_i0_lt_mapLen h_len_le_i_map h_take_i_map_eq_map h_get_map); done
    have h_map_get_eq : (List.map (replChar oldChar newChar) s.toList)[i0]! = replChar oldChar newChar (s.toList[i0]!) := by (try simp at *; expose_names); exact (goal_2_4 s oldChar newChar require_1 i out invariant_inv_bounds i_1 out_1 invariant_inv_out_list done_1 i_2 h_out_eq_out1 h_i_eq_len h_out_data_eq_map h_out_toList_eq_map h_len_part_out i0 hi0 h_i0_lt_mapLen h_len_le_i_map h_take_i_map_eq_map h_get_map h_out_get_eq); done
    exact by
      calc
        out.toList[i0]! = (List.map (replChar oldChar newChar) s.toList)[i0]! := by simpa using h_out_get_eq
        _ = replChar oldChar newChar (s.toList[i0]!) := by simpa using h_map_get_eq
  have h_post_out : postcondition s oldChar newChar out := by
    refine And.intro ?_ ?_
    · exact h_len_part_out
    · exact h_pointwise_part_out
  simpa [h_out_eq_out1] using h_post_out

prove_correct replaceChars by
  loom_solve <;> (try simp at *; expose_names)
  exact (goal_0 s oldChar newChar require_1 i out invariant_inv_bounds if_pos invariant_inv_out_list)
  exact (goal_1 s oldChar newChar require_1)
  exact (goal_2 s oldChar newChar require_1 i out invariant_inv_bounds i_1 out_1 invariant_inv_out_list done_1 i_2)
end Proof
