import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'


import CaseStudies.Velvet.Std

open PartialCorrectness DemonicChoice Lean.Elab.Term.DoNames

set_option auto.smt.trust true
set_option auto.smt true
--try increasing this parameter if verification fails
set_option auto.smt.timeout 4
set_option auto.smt.solver.name "cvc5"


attribute [solverHint] Array.get_set_c
section SpMV

--class for sparse vector
structure SpV (valTyp : Type) where
  ind: Array Nat
  val: Array valTyp
  size: ℕ
  size_eq: ind.size = size ∧ val.size = size
  inc: ∀ (i j: Nat), i < size → j < size →  i < j → ind[i]! < ind[j]!

def sumUpTo
  (spv : SpV Int)
  (v : Array Int) (bound : ℕ) : Int := ∑ i ∈ Finset.range bound, ((spv.val)[i]! * v[(spv.ind)[i]!]!)

@[grind, solverHint]
lemma sumUpToSucc
  (spv : SpV Int)
  (v : Array Int) (bound : ℕ) :
  sumUpTo spv v (bound + 1) = (sumUpTo spv v bound) +
    ((spv.val)[bound]! * v[(spv.ind)[bound]!]!) := by
  simp [sumUpTo]
  simp [@Finset.sum_range_succ]


--helpers for getElem syntax
instance : Inhabited (SpV Int) where
  default :=
  { ind := #[],
    val := #[],
    size := 0,
    size_eq := (by simp),
    inc := (fun i j h_i h_j i_lt_j => by simp [default]; omega) }
@[grind, solverHint]
lemma sumUpTo0
  (spv : SpV Int) (v : Array Int) :
  sumUpTo spv v 0 = 0 := by
  simp [sumUpTo]

instance: GetElem (SpV Int) Nat Int fun _ _ => True where
  getElem inst i _ :=
    match (List.zip (inst.ind.toList) (inst.val.toList)).find? fun (j, _) => j = i with
    | some pr => pr.2
    | none => 0

--sparse vector by vector multiplication
method VSpV
  (mut out: Array Int)
  (arr: Array Int)
  (spv: SpV Int) return (u: Unit)
  ensures outNew.size = 1
  ensures outNew[0]! = sumUpTo spv arr (spv.size)
  do
    let mut ind := 0
    out := Array.replicate 1 0
    while ind ≠ spv.size
    invariant out.size = 1
    invariant ind ≤ spv.size
    invariant out[0]! = sumUpTo spv arr ind
    done_with ind = spv.size
    do
      out[0] += (spv.val)[ind]! * arr[(spv.ind)[ind]!]!
      ind := ind + 1
    return

prove_correct VSpV by
  loom_solve

--CSR matrix by a vector multiplication
method spmv
  (mut out: Array Int)
  (arr: Array Int) (spv: SpV Int)
  (spm : Array (SpV Int)) return (u : Unit)
  ensures spm.size = outNew.size
  ensures ∀ i < spm.size, outNew[i]! = sumUpTo spm[i]! arr spm[i]!.size
  do
    out := Array.replicate spm.size 0
    let mut arrInd : Array Nat := Array.replicate spm.size 0
    let mut spmInd : Array Nat := Array.replicate spm.size 0
    while_some i :| i < arrInd.size ∧ arrInd[i]! < spm[i]!.size
    invariant arrInd.size = spm.size
    invariant out.size = spm.size
    invariant ∀ i < arrInd.size, arrInd[i]! <= spm[i]!.size
    invariant ∀ i < arrInd.size, out[i]! = sumUpTo spm[i]! arr arrInd[i]!
    done_with ∀ i < arrInd.size, arrInd[i]! = spm[i]!.size
    do
      let ind := arrInd[i]!
      let vInd := (spm[i]!.ind)[ind]!
      let mVal := (spm[i]!.val)[ind]!
      let val := mVal * arr[vInd]!
      out[i] += val
      arrInd[i] += 1
    return

prove_correct spmv by
  loom_solve

--helper function for calculation of dot product on sparse vectors
def spv_dot (spv1 spv2: SpV Int) (pnt1 pnt2: ℕ): Int :=
  if (spv1.size) ≤ pnt1 ∨ (spv2.size) ≤ pnt2 then
    0
  else
    if (spv1.ind)[pnt1]! = (spv2.ind)[pnt2]! then
      (spv1.val)[pnt1]! * (spv2.val)[pnt2]! + spv_dot spv1 spv2 (pnt1 + 1) (pnt2 + 1)
    else
      if (spv1.ind)[pnt1]! < (spv2.ind)[pnt2]! then
        spv_dot spv1 spv2 (pnt1 + 1) pnt2
      else
        spv_dot spv1 spv2 pnt1 (pnt2 + 1)
  termination_by ((spv1.size) + (spv2.size) - pnt1 - pnt2)

--sparse vector by sparse vector multiplication
method SpVSpV
  (mut out: Array Int)
  (spv1: SpV Int)
  (spv2: SpV Int) return (u: Unit)
  ensures outNew.size = 1
  ensures outNew[0]! = spv_dot spv1 spv2 0 0
  do
    out := Array.replicate 1 0
    let mut pnt1 := 0
    let mut pnt2 := 0
    while pnt1 ≠ spv1.size ∧ pnt2 ≠ spv2.size
    invariant out.size = 1
    invariant pnt1 ≤ spv1.size ∧ pnt2 ≤ spv2.size
    invariant out[0]! + spv_dot spv1 spv2 pnt1 pnt2 = spv_dot spv1 spv2 0 0
    done_with pnt1 = spv1.size ∨ pnt2 = spv2.size
    do
      if (spv1.ind)[pnt1]! = (spv2.ind)[pnt2]! then
        out[0] += (spv1.val)[pnt1]! * (spv2.val)[pnt2]!
        pnt1 := pnt1 + 1
        pnt2 := pnt2 + 1
      else
        if (spv1.ind)[pnt1]! < (spv2.ind)[pnt2]! then
          pnt1 := pnt1 + 1
        else
          pnt2 := pnt2 + 1
    return

--Compressed Sparse Row matrix by sparse vector multiplicaiton
method SpMSpV
  (mut out: Array Int)
  (spm: Array (SpV Int))
  (spv: SpV Int) return (u: Unit)
  ensures outNew.size = spm.size
  ensures ∀ i < spm.size, outNew[i]! = spv_dot spm[i]! spv 0 0
  do
    out := Array.replicate spm.size 0
    let mut spmInd := Array.replicate spm.size 0
    let mut spvInd := Array.replicate spm.size 0
    while_some i :| i < spm.size ∧ spmInd[i]! < spm[i]!.size ∧ spvInd[i]! < spv.size
    invariant spvInd.size = spm.size
    invariant spmInd.size = spm.size
    invariant out.size = spm.size
    invariant ∀ i < spmInd.size, spmInd[i]! <= spm[i]!.size
    invariant ∀ i < spvInd.size, spvInd[i]! <= spv.size
    invariant ∀ i < spm.size, out[i]! + spv_dot spm[i]! spv spmInd[i]! spvInd[i]! = spv_dot spm[i]! spv 0 0
    done_with ∀ i < spm.size, spmInd[i]! = spm[i]!.size ∨ spvInd[i]! = spv.size
    do
      let ind_m := spmInd[i]!
      let ind_v := spvInd[i]!
      if spm[i]!.ind[ind_m]! = spv.ind[ind_v]! then
        out[i] += spm[i]!.val[ind_m]! * spv.val[ind_v]!
        spmInd[i] += 1
        spvInd[i] += 1
      else
        if spm[i]!.ind[ind_m]! < spv.ind[ind_v]! then
          spmInd[i] += 1
        else
          spvInd[i] += 1
    return

--lemma for helper function
@[solverHint]
lemma spv_dot_eq
  (spv1 spv2: SpV Int) (pnt1 pnt2: ℕ) (prev: Int):
  prev + spv_dot spv1 spv2 pnt1 pnt2 = spv_dot spv1 spv2 0 0 →
    spv1.ind[pnt1]! = spv2.ind[pnt2]! →
    pnt1 < spv1.size →
    pnt2 < spv2.size →
    prev + spv1.val[pnt1]! * spv2.val[pnt2]! + spv_dot spv1 spv2 (pnt1 + 1) (pnt2 + 1) = spv_dot spv1 spv2 0 0 := by
      intro sum_eq ind_eq inb1 inb2
      rw [spv_dot] at sum_eq
      have neq: ¬(spv1.size ≤ pnt1 ∨ spv2.size ≤ pnt2) := by omega
      simp [neq, ind_eq] at sum_eq
      rw [←add_assoc] at sum_eq
      exact sum_eq

--lemma for helper function
@[solverHint]
theorem spv_dot_lt
  (spv1 spv2: SpV Int) (pnt1 pnt2: ℕ) (prev: Int):
  prev + spv_dot spv1 spv2 pnt1 pnt2 = spv_dot spv1 spv2 0 0 →
  spv1.ind[pnt1]! < spv2.ind[pnt2]! →
  pnt1 < spv1.size → pnt2 < spv2.size →
    prev + spv_dot spv1 spv2 (pnt1 + 1) pnt2 = spv_dot spv1 spv2 0 0 := by
      intro sum_eq ind_lt inb1 inb2
      rw [spv_dot] at sum_eq
      have neq: ¬(spv1.size ≤ pnt1 ∨ spv2.size ≤ pnt2) := by omega
      try simp only [loomAbstractionSimp] at *
      simp [neq, ind_lt] at sum_eq
      simp [lt_iff_le_and_ne.mp ind_lt] at sum_eq
      exact sum_eq

--lemma for helper function
@[solverHint]
theorem spv_dot_gt
  (spv1 spv2: SpV Int) (pnt1 pnt2: ℕ) (prev: Int) :
  prev + spv_dot spv1 spv2 pnt1 pnt2 = spv_dot spv1 spv2 0 0 →
  spv2.ind[pnt2]! ≤ spv1.ind[pnt1]! →
  spv1.ind[pnt1]! ≠ spv2.ind[pnt2]! →
  pnt1 < spv1.size → pnt2 < spv2.size →
    prev + spv_dot spv1 spv2 pnt1 (pnt2 + 1) = spv_dot spv1 spv2 0 0 := by
      intro sum_eq ind_le ind_neq inb1 inb2
      rw [spv_dot] at sum_eq
      have neq: ¬(spv1.size ≤ pnt1 ∨ spv2.size ≤ pnt2) := by omega
      try simp only [loomAbstractionSimp] at *
      simp [neq, ind_neq] at sum_eq
      have ilt: ¬(spv1.ind[pnt1]! < spv2.ind[pnt2]!) := by omega
      simp [ilt] at sum_eq
      exact sum_eq

--lemma for helper function
@[solverHint]
theorem spv_dot_exh
  (spv1 spv2: SpV Int) (pnt1 pnt2: ℕ):
  pnt1 = spv1.size ∨ pnt2 = spv2.size → spv_dot spv1 spv2 pnt1 pnt2 = 0 := by
    intro exh
    rw [spv_dot]
    by_cases triv: spv1.size ≤ pnt1 ∨ spv2.size ≤ pnt2 <;> simp [triv]
    omega

--proofs for sparse vector by sparse vector multiplication
--and sparse matrix by sparse vector multiplication algorithms
prove_correct SpVSpV by
  loom_solve <;> loom_auto

prove_correct SpMSpV by
  loom_solve <;> loom_auto

--now we will prove that presented algorithms indeed calculate
--dot product/matrix product


--theorem: getting a value by position which exists in sparse vector equals to element on that position
theorem getValSpV_eq (spv: SpV Int) (j: ℕ) (h_ind: j < spv.size): spv[spv.ind[j]!] = (spv.val)[j]! := by
  unfold getElem instGetElemSpVIntNatTrue; simp
  have just_case:
    List.find?
      (fun x ↦ decide (x.1 = spv.ind[j]!))
      (List.zip (spv.ind.toList) (spv.val.toList)) = some (((spv.ind)[j]!, (spv.val)[j]!)):= by
    apply List.find?_eq_some_iff_getElem.mpr
    simp
    exists j; rcases spv with ⟨ind, val, size, ⟨ind_size_eq, val_size_eq⟩, inc⟩ <;> simp at *
    rw [←ind_size_eq] at h_ind
    grind
  simp at just_case
  simp [just_case]


--theorem: getting a value by position which does exist in sparse vector equals to 0
theorem getValSpV_empty (spv: SpV Int) (j: ℕ) (h_empty: ∀ i < spv.size, spv.ind[i]! ≠ j): spv[j] = 0 := by
  simp [getElem]
  have none_case: List.find? (fun x ↦ decide (x.1 = j)) (List.zip (spv.ind.toList) (spv.val.toList)) = none := by
    apply List.find?_eq_none.mpr
    rintro x x_in; simp
    have zip_part := List.of_mem_zip x_in; simp [List.mem_iff_get] at zip_part
    rcases zip_part.left with ⟨i, hi⟩; have neq := h_empty i (have ilt := i.isLt; by simp [spv.size_eq] at ilt; simp [ilt])
    simp [hi] at neq; simp [neq]
  simp [none_case]

--theorem: sumUpTo helper equals to actual dot product for sparse vector by vector multiplication
theorem VSpV_correct_pure (out: Array Int) (arr: Array Int)
  (spv: SpV Int)
  (h_b: ∀ i < spv.size, spv.ind[i]! < arr.size):
  out.size = 1 → out[0]! = sumUpTo spv arr spv.size →
    out[0]! = ∑ i ∈ Finset.range (arr.size), spv[i] * arr[i]! := by
      intro sz sum_eq
      rw [sum_eq, sumUpTo]
      have ind_lemma: ∀ k, k ≤ arr.size →
        ∑ i ∈ Finset.range (spv.size), (if spv.ind[i]! < k then spv.val[i]! * arr[spv.ind[i]!]! else 0) =
        ∑ i ∈ Finset.range k, spv[i] * arr[i]! := by
          intro k
          induction k with
          | zero =>
            simp
          | succ m hm =>
            intro lt_m
            simp [Finset.sum_range_succ]
            rw [←hm (by omega)]
            have splitted_sum:
              (∑ i ∈ Finset.range (spv.ind.size), if spv.ind[i]! < m then spv.val[i]! * arr[spv.ind[i]!]! else 0) +
              (∑ i ∈ Finset.range (spv.ind.size), if spv.ind[i]! = m then spv.val[i]! * arr[spv.ind[i]!]! else 0) =
              (∑ i ∈ Finset.range (spv.ind.size), if spv.ind[i]! < m + 1 then spv.val[i]! * arr[spv.ind[i]!]! else 0) := by
                rw [←Finset.sum_add_distrib]
                rw [Finset.sum_congr (by rfl)]
                intro x hx
                by_cases h_eq_m : spv.ind[x]! = m <;> simp [h_eq_m]
                have miff : spv.ind[x]! < m ↔ spv.ind[x]! < m + 1 := by
                  constructor <;> rintro h_lt <;> omega
                simp [miff]
            rw [←spv.size_eq.1, ←splitted_sum, add_left_cancel_iff.mpr]
            by_cases exists_i: ∃ i < spv.size, spv.ind[i]! = m
            { rcases exists_i with ⟨ind, h_ind⟩
              rw [← h_ind.right]
              have lemma_res := getValSpV_eq spv ind h_ind.left
              simp at lemma_res
              simp [lemma_res]
              have almost_zero : ∀ i ∈ Finset.range (spv.ind.size), i ≠ ind →
                ((if spv.ind[i]! = spv.ind[ind]! then spv.val[i]! * arr[spv.ind[i]!]! else 0) = 0) := by
                  intro i i_inb i_not_ind
                  by_cases vind_eq : spv.ind[i]! = spv.ind[ind]!
                  { simp at i_inb
                    have i_sz: i < spv.size := by
                      rw [spv.size_eq.1] at i_inb
                      exact i_inb
                    rcases lt_or_gt_of_ne i_not_ind with i_lt | inb_lt
                    { simp [getElem, Nat.lt_iff_le_and_ne.mp (spv.inc i ind i_sz h_ind.left i_lt)] }
                    have lt := Nat.lt_iff_le_and_ne.mp (spv.inc ind i h_ind.left i_sz inb_lt)
                    simp [getElem] at vind_eq
                    simp [vind_eq] at lt }
                  simp [vind_eq]
              have ind_inb: ind ∉ Finset.range (spv.size) →
                ((if spv.ind[ind]! = spv.ind[ind]! then spv.val[ind]! * arr[spv.ind[ind]!]! else 0) = 0) := by
                  intro ind_not_inb
                  simp at ind_not_inb
                  omega
              rw [←spv.size_eq.1] at ind_inb
              simp [Finset.sum_eq_single ind almost_zero ind_inb] }
            simp at exists_i
            have h_getVal := getValSpV_empty spv m exists_i
            simp at h_getVal
            simp [h_getVal]
            apply Finset.sum_eq_zero
            rintro x hx
            by_cases h_eq: spv.ind[x]! = m <;> simp [h_eq]
            simp [←h_eq] at h_getVal
            simp at hx
            rw [spv.size_eq.1] at hx
            simp [getValSpV_eq spv x hx] at h_getVal
            simp [h_getVal]
      have fin_lemma := ind_lemma (arr.size) (by rfl)
      rw [←fin_lemma]
      exact Finset.sum_congr (by rfl) fun i h_i => by aesop

--sparse vector by vector multiplication algorithm actually computes dot product
theorem VSpV_correct_triple (out: Array Int) (arr: Array Int) (spv: SpV Int):
  triple
    (∀ i < spv.size, spv.ind[i]! < arr.size)
    (VSpV out arr spv)
    fun ⟨_, ⟨outNew, PUnit.unit⟩⟩ =>
      outNew[0]! = ∑ i ∈ Finset.range (arr.size), spv[i] * arr[i]! := by
      simp [triple]
      intro h_b
      apply wp_cons (VSpV out arr spv)
        fun ⟨u, ⟨outNew, PUnit.unit⟩⟩ =>
          (outNew[0]! = sumUpTo spv arr spv.size ∧ outNew.size = 1)
      { rintro ⟨u, ⟨outNew⟩⟩; simp
        intro sum_eq sz
        exact VSpV_correct_pure outNew arr spv h_b sz sum_eq }
      simp
      have triple_true := VSpV_correct out arr spv
      simp [triple] at triple_true
      apply triple_true

--Column Sparse Matrix by vector multiplication algorithm actually computes matrix multiplication
theorem spmv_correct_triple (out: Array Int) (arr: Array Int) (spm: Array (SpV Int)):
  triple
    (∀ i < spm.size, ∀ j < spm[i]!.size, spm[i]!.ind[j]! < arr.size)
    (spmv out arr spv spm)
    fun ⟨_, ⟨outNew, _⟩⟩ =>
      (∀ j < outNew.size, outNew[j]! = ∑ i ∈ Finset.range (arr.size), spm[j]![i] * arr[i]!) := by
      simp [triple]
      intro h_b
      apply wp_cons
        (spmv out arr spv spm)
        fun ⟨_, ⟨outNew, _⟩⟩ =>
          ((∀ i < spm.size, outNew[i]! = sumUpTo spm[i]! arr spm[i]!.size) ∧ spm.size = outNew.size)
      { simp; rintro ⟨_, ⟨outNew⟩⟩; simp
        intro sum_eq sz_eq j h_j
        have single_elem : (Array.replicate 1 outNew[j]!)[0]! = outNew[j]! := by
          simp
          -- simp [getElem!] at replicate_get
          -- simp [getElem, replicate_get]
        have single_th := VSpV_correct_pure
          (Array.replicate 1 outNew[j]!)
          arr
          spm[j]!
          (h_b j (by rw [←sz_eq] at h_j; exact h_j))
          (by simp)
          (by simp; exact sum_eq j (by rw [←sz_eq] at h_j; exact h_j))
        simp at single_th
        simp [←single_th] }
      simp
      have triple_true := spmv_correct out arr spv spm
      simp [triple] at triple_true
      exact triple_true

--theorem: helper function computes actual dot product
theorem spv_dot_pure_gen (spv1: SpV Int) (spv2: SpV Int) (n pnt1 pnt2: ℕ)
  (sz1: ∀ i < spv1.size, spv1.ind[i]! < n)
  (sz2: ∀ i < spv2.size, spv2.ind[i]! < n):
  spv_dot spv1 spv2 pnt1 pnt2 =
    ∑ i ∈ Finset.range n,
      if max
        (if spv1.size ≤ pnt1 then n else spv1.ind[pnt1]!)
        (if spv2.size ≤ pnt2 then n else spv2.ind[pnt2]!) ≤ i then
        spv1[i] * spv2[i]
      else
        0 := by
  fun_induction spv_dot spv1 spv2 pnt1 pnt2 with
  | case1 p1 p2 h =>
    have all_zero: (∀ x ∈ Finset.range n, (if max (if spv1.size ≤ p1 then n else spv1.ind[p1]!) (if spv2.size ≤ p2 then n else spv2.ind[p2]!) ≤ x then spv1[x] * spv2[x] else 0) = 0) := by
      intro x hx
      simp
      rcases h with ob1 | ob2
      { simp [ob1]
        simp at hx
        simp [hx] }
      simp [ob2]
      simp at hx
      simp [hx]
    rw [Finset.sum_eq_zero all_zero]
  | case2 p1 p2 h1 eq ih =>
    rw [ih, ←getValSpV_eq spv1 p1 (by omega), ←getValSpV_eq spv2 p2 (by omega)]
    have sum_eq_single:
      ∑ i ∈ Finset.range n, (if i = spv1.ind[p1]! then spv1[spv1.ind[p1]!] * spv2[spv1.ind[p1]!] else 0) = (if spv1.ind[p1]! = spv1.ind[p1]! then spv1[spv1.ind[p1]!] * spv2[spv1.ind[p1]!] else 0) := by
      have hb: ∀ i ∈ Finset.range n, i ≠ spv1.ind[p1]! → ((if i = spv1.ind[p1]! then spv1[spv1.ind[p1]!]! * spv2[spv1.ind[p1]!]! else 0) = 0) := by
        intro i hi iq
        simp at hi
        simp [iq]
      have hc: spv1.ind[p1]! ∉ Finset.range n → ((if spv1.ind[p1]! = spv1.ind[p1]! then spv1[spv1.ind[p1]!]! * spv2[spv1.ind[p1]!]! else 0) = 0) := by
        intro nin
        simp at nin
        have bnd := sz1 p1 (by omega)
        omega
      apply Finset.sum_eq_single spv1.ind[p1]! hb hc
    rw [if_pos] at sum_eq_single
    rw [←eq, ←sum_eq_single]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr
    { rfl }
    intro x hx
    simp at hx
    have h2: ¬spv1.size ≤ p1 ∧ ¬spv2.size ≤ p2 := by omega
    simp [h2]
    have hnx: ¬(n ≤ x) := by simp [hx]
    by_cases xeq: x = spv1.ind[p1]! <;> simp [xeq]
    { intro in1 in2
      by_cases edg1: spv1.size ≤ p1 + 1 <;> simp [edg1] at in1
      { omega }
      have p1lt := (spv1.inc) p1 (p1 + 1) (by omega) (by omega) (by simp)
      -- simp [getElem] at in1
      omega }
    have outb_lemma (spv: SpV Int) (pos: ℕ) (hsz: 1 ≤ spv.size) (hb: spv.ind[spv.size - 1]! < pos): spv[pos] = 0 := by
      by_cases ex: ∃ i < spv.size, spv.ind[i]! = pos
      { rcases ex with ⟨i, hbi, hi⟩
        by_cases heq: i = spv.size - 1
        { simp [heq] at hi
          omega }
        have contra := (spv.inc) i (spv.size - 1) (by omega) (by omega) (by omega)
        simp at hb
        -- simp [getElem] at hi
        omega }
      simp at ex
      simp [getValSpV_empty spv pos ex]
    by_cases edg1: spv1.size ≤ p1 + 1 <;> simp [edg1]
    { simp [hnx]
      have p1eq : p1 = spv1.size - 1 := by omega
      by_cases lex: spv1.ind[p1]! ≤ x <;> simp [lex]
      have ltx: spv1.ind[p1]! < x := by omega
      simp [p1eq] at ltx
      simp [outb_lemma spv1 x (by omega) ltx] }
    by_cases edg2: spv2.size ≤ p2 + 1 <;> simp [edg2]
    { simp [hnx]
      by_cases lex: spv1.ind[p1]! ≤ x <;> simp [lex]
      have ltx: spv1.ind[p1]! < x := by omega
      have p2eq: p2 = spv2.size - 1 := by omega
      simp [eq, p2eq] at ltx
      simp [outb_lemma spv2 x (by omega) ltx] }
    by_cases val: spv1.ind[p1 + 1]! ≤ x ∧ spv2.ind[p2 + 1]! ≤ x <;> simp [val]
    { have inc: spv1.ind[p1]! < spv1.ind[p1 + 1]! := (spv1.inc) p1 (p1 + 1) (by omega) (by omega) (by simp)
      simp [le_of_lt (lt_of_lt_of_le inc val.left)] }
    by_cases xb: spv1.ind[p1]! ≤ x <;> simp [xb]
    have ltx: spv1.ind[p1]! < x := by omega
    simp at val
    have interm_lemma (spv: SpV Int) (pos idx: ℕ) (hsz: idx + 1 < spv.size) (inter: spv.ind[idx]! < pos ∧ pos < spv.ind[idx + 1]!): spv[pos] = 0 := by
      by_cases ex: ∃ i < spv.size, spv.ind[i]! = pos
      { rcases ex with ⟨i, hbi, hi⟩
        have lt_lemma (i1 i2: ℕ) (hi1: i1 < spv.size) (hi2: i2 < spv.size): spv.ind[i1]! < spv.ind[i2]! → i1 < i2 := by
          intro hlt
          by_cases contra_lt: i2 < i1
          { have inc := spv.inc i2 i1 hi2 hi1 contra_lt
            simp at hlt
            omega }
          by_cases contra_eq: i1 = i2
          { simp [contra_eq] at hlt }
          omega
        have left_x := lt_lemma idx i (by omega) (by omega) (by omega)
        have right_x := lt_lemma i (idx + 1) (by omega) (by omega) (by omega)
        omega }
      simp at ex
      simp [getValSpV_empty spv pos ex]
    rcases (em (spv1.ind[p1 + 1]! ≤ x)) with c1 | c2
    { simp [c1] at val
      simp [interm_lemma spv2 x p2 (by omega) (by omega)] }
    simp at c2
    simp [interm_lemma spv1 x p1 (by omega) (by omega)]
    rfl
  | case3 p1 p2 h1 neq le ih =>
    rw [ih]
    apply Finset.sum_congr
    { rfl }
    intro x hx
    by_cases edg: spv1.size = p1 + 1
    { have sz_concl := sz1 p1 (by omega)
      simp [edg]
      simp at hx
      have nx : ¬(n ≤ x) := by omega
      by_cases b2: spv2.size ≤ p2 <;> simp [b2] <;> simp [nx]
      intro ifc1 ifc2
      by_cases ex: ∃ i < spv1.size, spv1.ind[i]! = x
      { rcases ex with ⟨i, ib, hi⟩
        by_cases il: p1 < i
        { omega }
        simp at il
        rcases (le_iff_eq_or_lt.mp il) with ieq | ilt
        { simp [ieq] at hi
          omega }
        have contra := spv1.inc i p1 ib (by omega) ilt
        omega }
      simp at ex
      simp [getValSpV_empty spv1 x ex] }
    have inb: ¬(spv1.size ≤ p1 + 1) ∧ ¬(spv1.size ≤ p1):= by omega
    simp [inb]
    by_cases edg2: spv2.size ≤ p2 <;> simp [edg2]
    { simp at hx
      have neg: ¬ (n ≤ x) := by omega
      simp [neg] }
    by_cases le2: spv2.ind[p2]! ≤ x <;> simp [le2]
    by_cases upper: spv1.ind[p1 + 1]! ≤ x <;> simp [upper]
    { simp at inb
      simp [getElem]
      simp [le_trans (le_of_lt (spv1.inc p1 (p1 + 1) inb.right inb.left (by simp))) upper] }
    by_cases lower: spv1.ind[p1]! ≤ x <;> simp [lower]
    by_cases ex: ∃ i < spv1.size, spv1.ind[i]! = x
    { rcases ex with ⟨ind, indb, hind⟩
      by_cases ind_x: ind = p1
      { simp [ind_x] at hind
        omega }
      rcases (lt_or_gt_of_ne ind_x) with ltc | gtc
      { have contra := spv1.inc ind p1 indb (by omega) ltc
        -- simp [getElem] at lower
        -- simp [getElem] at hind
        omega }
      by_cases indp1: ind = p1 + 1
      { simp [indp1] at hind
        omega }
      have indlt: p1 + 1 < ind := by omega
      have contra := spv1.inc (p1 + 1) ind (by omega) indb indlt
      -- simp [getElem] at upper
      -- simp [getElem] at hind
      omega }
    simp at ex
    simp [getValSpV_empty spv1 x ex]
  | case4 p1 p2 h1 neq nle ih =>
    rw [ih]
    apply Finset.sum_congr
    { rfl }
    intro x hx
    by_cases edg: spv2.size = p2 + 1
    { have sz_concl := sz2 p2 (by omega)
      simp [edg]
      simp at hx
      have nx : ¬(n ≤ x) := by omega
      by_cases b1: spv1.size ≤ p1 <;> simp [b1] <;> simp [nx]
      intro ifc1 ifc2
      by_cases ex: ∃ i < spv2.size, spv2.ind[i]! = x
      { rcases ex with ⟨i, ib, hi⟩
        by_cases il: p2 < i
        { omega }
        simp at il
        rcases (le_iff_eq_or_lt.mp il) with ieq | ilt
        { simp [ieq] at hi
          omega }
        have contra := (spv2.inc) i p2 ib (by omega) ilt
        -- simp [getElem] at hi
        -- simp [getElem] at ifc2
        omega }
      simp at ex
      simp [getValSpV_empty spv2 x ex] }
    have inb: ¬(spv2.size ≤ p2 + 1) ∧ ¬(spv2.size ≤ p2):= by omega
    simp [inb]
    by_cases edg1: spv1.size ≤ p1 <;> simp [edg1]
    { simp at hx
      have neg: ¬ (n ≤ x) := by omega
      simp [neg] }
    by_cases le1: spv1.ind[p1]! ≤ x <;> simp [le1]
    by_cases upper: spv2.ind[p2 + 1]! ≤ x <;> simp [upper]
    { simp at inb
      simp [getElem]
      simp [le_trans (le_of_lt ((spv2.inc) p2 (p2 + 1) inb.right inb.left (by simp))) upper] }
    by_cases lower: spv2.ind[p2]! ≤ x <;> simp [lower]
    by_cases ex: ∃ i < spv2.size, spv2.ind[i]! = x
    { rcases ex with ⟨ind, indb, hind⟩
      by_cases ind_x: ind = p2
      { simp [ind_x] at hind
        omega }
      rcases (lt_or_gt_of_ne ind_x) with ltc | gtc
      { have contra := (spv2.inc) ind p2 indb (by omega) ltc
        -- simp [getElem] at lower
        -- simp [getElem] at hind
        omega }
      by_cases indp2: ind = p2 + 1
      { simp [indp2] at hind
        omega }
      have indlt: p2 + 1 < ind := by omega
      have contra := (spv2.inc) (p2 + 1) ind (by omega) indb indlt
      -- simp [getElem] at upper
      -- simp [getElem] at hind
      omega }
    simp at ex
    simp [getValSpV_empty spv2 x ex]

--theorem: helper function from (0,0) calculates full dot product
theorem spv_dot_pure (spv1 spv2: SpV Int) (n: ℕ)
  (sz1: ∀ i < spv1.size, spv1.ind[i]! < n) (sz2: ∀ i < spv2.size, spv2.ind[i]! < n):
    spv_dot spv1 spv2 0 0 = ∑ i ∈ Finset.range n, spv1[i] * spv2[i] := by
      simp [spv_dot_pure_gen spv1 spv2 n 0 0 sz1 sz2]
      apply Finset.sum_congr
      { rfl }
      intro x hx
      simp at hx
      by_cases em1: spv1.size = 0 <;> simp [em1]
      { simp [lt_iff_le_not_ge.mp hx]
        simp [getValSpV_empty spv1 x (by intro i hi; omega)] }
      by_cases em2: spv2.size = 0 <;> simp [em2]
      { intros
        simp [getValSpV_empty spv2 x (by intro i hi; omega)] }
      intro zer_ineq
      have zer_lemma (spv: SpV Int) (i: ℕ) (hsz: spv.size ≠ 0): i < spv.ind[0]! → spv[i] = 0 := by
        intro lt
        have all_none: ∀ j < spv.size, spv.ind[j]! ≠ i := by
          intro i1 hi1
          by_cases i10 : i1 = 0
          { simp [←i10] at lt
            omega }
          have contra := spv.inc 0 i1 (by omega) (by omega) (by omega)
          simp at lt
          omega
        simp [getValSpV_empty spv i all_none]
      by_cases sm1: spv1.ind[0]! ≤ x
      { simp [sm1] at zer_ineq
        simp [zer_lemma spv2 x em2 zer_ineq] }
      simp at sm1
      simp [zer_lemma spv1 x em1 sm1]

--sparse vector by sparse vector multiplicaiton algorithm actually computes dot product
theorem SpVSpV_correct_triple (out: Array Int) (spv1 spv2: SpV Int) (n: ℕ):
  triple
    ((∀ i < spv1.size, spv1.ind[i]! < n) ∧ (∀ i < spv2.size, spv2.ind[i]! < n))
    (SpVSpV out spv1 spv2)
    fun ⟨_, ⟨outNew, PUnit.unit⟩⟩ =>
      outNew[0]! = ∑ i ∈ Finset.range n, spv1[i]! * spv2[i]! := by
      simp [triple]
      intro b1 b2
      apply wp_cons (SpVSpV out spv1 spv2)
        fun ⟨_, ⟨outNew, PUnit.unit⟩⟩ =>
          outNew[0]! = spv_dot spv1 spv2 0 0 ∧ outNew.size = 1
      { rintro ⟨_, ⟨outNew, PUnit.unit⟩⟩; simp
        intro sum_eq sz_eq
        simp [sum_eq]
        exact spv_dot_pure spv1 spv2 n b1 b2 }
      simp
      have triple_true := SpVSpV_correct out spv1 spv2
      simp [triple] at triple_true
      simp [WithName] at triple_true
      exact triple_true

--Compressed Sparse Row matrix by sparse vector multiplicaiton algorithm actually computes matrix product
theorem SpMSpV_correct_triple
  (out: Array Int)
  (spm: Array (SpV Int))
  (spv: SpV Int)
  (n: ℕ):
  triple
    (∀ i < spm.size, (∀ j < spm[i]!.size, spm[i]!.ind[j]! < n) ∧ (∀ j < spv.size, spv.ind[j]! < n))
    (SpMSpV out spm spv)
    fun ⟨_, ⟨outNew, _⟩⟩ =>
      outNew.size = spm.size ∧ ∀ i < spm.size, outNew[i]! = ∑ idx ∈ Finset.range n, spm[i]![idx]! * spv[idx]! := by
        simp [triple]
        intro inb
        apply wp_cons (SpMSpV out spm spv)
          fun ⟨_, ⟨outNew, _⟩⟩ =>
            (∀ i < spm.size, outNew[i]! = spv_dot spm[i]! spv 0 0) ∧ outNew.size = spm.size
        { rintro ⟨_, ⟨outNew, _⟩⟩; simp
          intro sum_eq sz_eq
          simp [sz_eq]
          intro i ib
          simp [←spv_dot_pure spm[i]! spv n (inb i ib).left (inb i ib).right]
          exact sum_eq i ib }
        simp
        have triple_true := SpMSpV_correct out spm spv
        simp [triple] at triple_true
        simp [WithName] at triple_true
        exact triple_true

end SpMV
