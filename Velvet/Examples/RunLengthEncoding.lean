import Velvet

open Std.WP

structure Encoding where
  cnt : Nat
  c : Char
deriving Inhabited

def getCntSum (l : List Encoding) : Nat :=
  match l with
  | [] => 0
  | e :: xs => e.cnt + getCntSum xs

@[grind =]
theorem getCntSum_cons (e : Encoding) (l : List Encoding) :
    getCntSum (e :: l) = e.cnt + getCntSum l := rfl

@[grind =]
theorem getCntSum_nil : getCntSum [] = 0 := rfl

@[grind =]
theorem take_array_size (arr : Array Encoding) :
    arr.toList.take arr.size = arr.toList := by
  have h : arr.size = arr.toList.length := Array.length_toList.symm
  rw [h, List.take_length]

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

@[grind =]
theorem getCntSum_take_succ' (l : List Encoding) (i : Nat) (h : i < l.length) :
    getCntSum (l.take (i + 1)) = getCntSum (l.take i) + l[i].cnt :=
  getCntSum_take_succ h (e := l[i]) rfl

@[grind =]
theorem array_size_append_replicate (a : Array Char) (n : Nat) (c : Char) :
    (a ++ Array.replicate n c).size = a.size + n := by
  simp

@[grind =]
theorem getElem!_eq_toList_getElem (arr : Array Encoding) (i : Nat) (h : i < arr.size) :
    arr[i]! = arr.toList[i]'(by simpa using h) := by
  simp [h]

@[reducible]
def isValidRunSequence (encoded : Array Encoding) : Prop :=
  ∀ i, (h : i < encoded.size) → (encoded[i]'h).cnt > 0

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
  velvet_vcgen [decodeStr] with finish

@[grind]
def decodeStrLean (encoded_str : Array Encoding) : Array Char :=
  let mp := Array.map (fun e => Array.replicate e.cnt e.c) encoded_str
  mp.flatten

method encodeStr (str : Array Char)
  returns (res : Array Encoding)
  ensures valid: isValidRunSequence res
  ensures decoded_eq: decodeStrLean res = str
do
  let mut encoding : Array Encoding := #[]
  let mut i : Nat := 0
  while' loop_i: i < str.size
    invariant i_bounded: i ≤ str.size
    invariant decoded_inv: decodeStrLean encoding = str.extract 0 i
    invariant valid_inv: isValidRunSequence encoding
    decreasing loop_cntr: str.size - i
  do
    let curChar := str[i]!
    let mut j : Nat := i + 1
    while' loop_j: j < str.size ∧ str[j]! == curChar
      invariant j_bounds: i < j ∧ j ≤ str.size
      invariant all_eq: ∀ k, i ≤ k → k < j → str[k]! = curChar
      decreasing loop_j_cntr: str.size - j
    do
      j := j + 1
    let cnt := j - i
    encoding := encoding.push ({cnt := cnt, c := curChar})
    i := j
  return encoding

prove_correct encodeStr by
  velvet_vcgen [encodeStr] with finish
