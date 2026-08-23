import Velvet2.Syntax
import Velvet2.VCGen.Frontend

open Std.Internal.Do

structure Encoding where
  cnt : Nat
  c : Char
deriving Inhabited

def getCntSum (l : List Encoding) : Nat :=
  match l with
  | [] => 0
  | e :: xs => e.cnt + getCntSum xs

@[grind]
theorem getCntSum_cons (e : Encoding) (l : List Encoding) :
    getCntSum (e :: l) = e.cnt + getCntSum l := rfl

@[grind]
theorem getCntSum_nil : getCntSum [] = 0 := rfl

theorem getCntSum_append (l1 l2 : List Encoding) :
    getCntSum (l1 ++ l2) = getCntSum l1 + getCntSum l2 := by
  induction l1 with
  | nil => simp only [List.nil_append, getCntSum_nil]; omega
  | cons e t ih =>
      simp only [List.cons_append, getCntSum_cons]
      omega

@[reducible]
def isValidRunSequence (encoded : Array Encoding) : Prop :=
  ∀ i, (h : i < encoded.size) → (encoded[i]'h).cnt > 0

/-- Bridge between a prefix `extract` and `List.take`. -/
@[simp]
theorem extract_take_toList {α : Type} (arr : Array α) (i : Nat) :
    (arr.extract 0 i).toList = arr.toList.take i := by
  simp [Array.toList_extract, List.extract_eq_take_drop]

/-- Peeling one more element off a `take` prefix adds its count. -/
theorem getCntSum_take_succ {l : List Encoding} {i : Nat} (h : i < l.length)
    {e : Encoding} (he : l[i] = e) :
    getCntSum (l.take (i + 1)) = getCntSum (l.take i) + e.cnt := by
  cases i with
  | zero =>
      cases l with
      | nil => simp at h
      | cons f t =>
          have hf : f = e := by simpa using he
          subst hf
          simp [getCntSum_cons, getCntSum_nil]
  | succ k =>
      cases l with
      | nil => simp at h
      | cons f t =>
          have hk : k < t.length := by simpa using h
          have htk : t[k] = e :=
            (List.getElem_cons_succ (h := by omega)).symm.trans he
          have hrec := getCntSum_take_succ hk htk
          show getCntSum ((f :: t).take (k + 1 + 1)) = _
          simp only [List.take_succ_cons, getCntSum_cons]
          rw [hrec]
          omega

method decodeStr (encoded : Array Encoding)
  returns (res : Array Char)
  requires valid: isValidRunSequence encoded
  ensures size_ok: res.size = getCntSum encoded.toList
do
  let mut decoded := #[]
  let mut i : Nat := 0
  while' loop_cond: i < encoded.size
    invariant idx_bounded: i ≤ encoded.size
    invariant size_inv: decoded.size = getCntSum (encoded.toList.take i)
    decreasing loop_cntr: encoded.size - i
    done_with done: i = encoded.size
  do
    let elem := encoded[i]!
    decoded := decoded ++ Array.replicate elem.cnt elem.c
    i := i + 1
  return decoded

prove_correct decodeStr by
  vcgen_ [decodeStr] simplifying_assumptions with try finish
  case size_ok =>
    rename_i encoded decoded i
    have h1 := size_inv
    rw [done] at h1
    have hsz : encoded.size = encoded.toList.length := by simp
    rw [hsz, List.take_length] at h1
    exact h1
  case size_inv =>
    rename_i encoded decoded i
    have hszlt : i < encoded.size := loop_cond
    have hlt : i < encoded.toList.length := by simpa using hszlt
    have hget : encoded.toList[i] = encoded[i]'hszlt :=
      Array.getElem_toList (xs := encoded) (i := i) hlt
    have hbang : encoded[i]'hszlt = encoded[i]! := by simp [hszlt]
    have hstep := getCntSum_take_succ (l := encoded.toList) (i := i) hlt
      (e := encoded[i]'hszlt) hget
    have hs : (decoded ++ Array.replicate encoded[i]!.cnt encoded[i]!.c).size =
        decoded.size + (encoded[i]'hszlt).cnt := by
      rw [hbang]
      simp [Array.size_append, Array.size_replicate]
    rw [hs, hstep, ← size_inv]
