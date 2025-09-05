import Auto
import Lean

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Int.Bitwise
import Mathlib.Init
import Mathlib.Data.Nat.Basic

import Loom.MonadAlgebras.NonDetT.Extract
import Loom.MonadAlgebras.WP.Tactic
import Loom.MonadAlgebras.WP.DoNames'

import CaseStudies.Velvet.Std

open TotalCorrectness DemonicChoice Lean.Elab.Term.DoNames

section


method abs(x : Int) return (r : Int)
ensures r >= 0
do
   if x >= 0 then return x
   else return x.neg

prove_correct abs by
  dsimp [abs]
  loom_solve
  · grind
  · grind


method MultipleReturns (x: Int) (y: Int) return (result : Int × Int)
  require 0 < y
  ensures x < result.fst
  ensures x > result.snd
  do
  let mut more := x + y;
  let mut less := x - y;
  return (more,less)


prove_correct MultipleReturns by
  dsimp [MultipleReturns]
  loom_solve <;> grind

end

structure LsbResult (i: Nat) where
    val : Nat
    val_gt : 0 < val
    val_leq : val <= i


def lsb (i: Nat) (iPos: i>0) : LsbResult i :=
    if h: Nat.bodd i then ⟨ 1, (by simp) ,(by grind)⟩ else (
       let ⟨val, val_gt, val_leq ⟩ := lsb i.boddDiv2.2 (by
          induction i
          · grind
          · simp [*] at h
            simp [h] 
       )
       {
       val := 2 * val,
       val_gt := (by grind),
       val_leq := (by
               simp [*] at *
               rw [Nat.mul_comm]
               rw [Nat.div2_val] at val_leq
               rw [← Nat.le_div_iff_mul_le (by decide)]
               assumption
          )
        }
    )
    termination_by i
    decreasing_by (
        simp     
        have iAtleastOne : i >= 1 := by grind
        have iNotOne : ¬( i = 1 ) := by
             intro h
             simp [*] at *
        have iAtleastTwo : i >= 2 := by grind
        apply Nat.binaryRec_decreasing
        omega
)

#eval lsb 6 (by grind)

-- easier to make the parameter a Nat, makes writing the invariant and dealing with it easier
def g (i: Nat) : Nat :=
    if h: i = 0 then 0 else (
        let ⟨val, val_gt, val_leq⟩ := lsb i (by omega)
        i - val
    )

inductive SumRange {sz} : (_l: Nat ) -> (_r: Nat ) -> (_arr: Vector Nat sz  )-> (_v: Nat) -> Prop where
    | base : ∀ (arr: Vector Nat sz) ( l r: Nat ),
                   (l >= r) -> SumRange l r arr 0
    | l : ∀ (arr: Vector Nat sz)
                   (l r v: Nat),
                   (hl: l < r) ->
                   (hr: r <= sz ) ->
                   (h: SumRange l.succ  r arr v) ->
                   SumRange l r arr (arr[l] +  v )

    | r : ∀ (arr: Vector Nat sz)
                   (l r v: Nat),
                   (hl: l < r.succ) ->
                   (hr: r.succ <= sz ) ->
                   (h: SumRange l r arr v) ->
                   SumRange l r.succ arr ( arr[r]+ v  )

structure Fen where
    sz: Nat
    arr: Vector Nat (sz + 1)
    inv: ∃ (a: Vector Nat sz),
         ∀ (i: Nat) (hi: i <= sz),
         SumRange (g i) i a arr[i]


def mkFen (n: Nat) : Fen :=
    let sz := n
    let arr := Vector.replicate (n+1) 0
    {
    sz,
    arr,
    inv := (by
        exists (Vector.replicate n 0)
        have all_elems_0 : ∀ (i: Nat) (h:i<=sz) , arr[i] = 0 := by
             grind
        intro i h
        induction i using Nat.case_strong_induction_on
        · unfold g; simp[*]
          apply SumRange.base
          grind
        · case hi i' ih =>
          have ihSpclForI' := ih i' (by simp) (by omega)
          rw [(all_elems_0 (i'+1) h)]
          rw [(all_elems_0 (i') (by grind))] at ihSpclForI'
          sorry
    )
    }

