module

public import Velvet
public meta import Velvet
public import Mathlib.Data.Int.ModEq

/-!
## Program description

Compute `x` raised to the natural-number power `n` modulo a positive integer
`p`, including negative bases and the cases `n = 0` and `p = 1`. The program is
expected to run in O(log n) time and O(1) extra space.
-/

namespace PowXN

section Specs

public def precondition (_x : Int) (_n : Nat) (p : Int) : Prop := p > 0

public def postcondition (x : Int) (n : Nat) (p result : Int) : Prop :=
  0 ≤ result ∧ result < p ∧ Int.ModEq p result (x ^ n)

end Specs

section Implementation

public def modularGo (p base : Int) (exp : Nat) (acc : Int) : Int :=
  match exp with
  | 0 => acc
  | Nat.succ exp' =>
    let e := Nat.succ exp'
    let acc' := if e % 2 = 1 then (acc * base) % p else acc
    modularGo p ((base * base) % p) (e / 2) acc'
termination_by exp

public def modularPow (x : Int) (n : Nat) (p : Int) : Int :=
  modularGo p (x % p) n ((1 : Int) % p)

method powMod (x : Int) (n : Nat) (p : Int)
  returns (result : Int)
  requires positive_modulus: precondition x n p
  ensures powered: postcondition x n p result
do
  let mut base := x % p
  let mut exp := n
  let mut acc := (1 : Int) % p
  while' positive_exp: exp ≠ 0
    invariant continuation: modularGo p base exp acc = modularPow x n p
    decreasing exponent: exp
    done_with finished: exp = 0
  do
    if odd: exp % 2 = 1 then
      acc := (acc * base) % p
    base := (base * base) % p
    exp := exp / 2
  return acc

end Implementation

section Proof

theorem modularGo_range (hp : 0 < p) :
    ∀ exp base acc, 0 ≤ acc → acc < p →
      0 ≤ modularGo p base exp acc ∧ modularGo p base exp acc < p := by
  intro exp
  induction exp using Nat.strongRecOn with
  | ind exp ih =>
      intro base acc hacc0 haccp
      cases exp with
      | zero => simpa [modularGo] using And.intro hacc0 haccp
      | succ exp' =>
          have hlt : Nat.succ exp' / 2 < Nat.succ exp' :=
            Nat.div_lt_self (Nat.succ_pos exp') (by decide)
          by_cases hodd : Nat.succ exp' % 2 = 1
          · have h0 : 0 ≤ (acc * base) % p := Int.emod_nonneg _ (by omega)
            have hp' : (acc * base) % p < p := Int.emod_lt_of_pos _ hp
            simpa [modularGo, hodd] using
              ih (Nat.succ exp' / 2) hlt ((base * base) % p)
                ((acc * base) % p) h0 hp'
          · simpa [modularGo, hodd] using
              ih (Nat.succ exp' / 2) hlt ((base * base) % p) acc hacc0 haccp

theorem square_pow (base : Int) (q : Nat) :
    (base * base) ^ q = base ^ (2 * q) := by
  rw [Int.mul_pow]
  rw [show 2 * q = q + q by omega, Int.pow_add]

theorem modularGo_modEq :
    ∀ exp base acc p, Int.ModEq p (modularGo p base exp acc) (acc * base ^ exp) := by
  intro exp
  induction exp using Nat.strongRecOn with
  | ind exp ih =>
      intro base acc p
      cases exp with
      | zero => simp [modularGo, Int.ModEq]
      | succ exp' =>
          let e := Nat.succ exp'
          have hlt : e / 2 < e := by
            simp only [e]
            exact Nat.div_lt_self (Nat.succ_pos exp') (by decide)
          have hdecomp := Nat.mod_add_div e 2
          by_cases hodd : e % 2 = 1
          · have he : e = 2 * (e / 2) + 1 := by omega
            let q := e / 2
            have hrec := ih (e / 2) hlt ((base * base) % p) ((acc * base) % p) p
            have hstep : Int.ModEq p
                (((acc * base) % p) * (((base * base) % p) ^ (e / 2)))
                ((acc * base) * ((base * base) ^ (e / 2))) :=
              Int.ModEq.mul (Int.mod_modEq _ _)
                (Int.ModEq.pow _ (Int.mod_modEq _ _))
            have halg : (acc * base) * ((base * base) ^ (e / 2)) =
                acc * base ^ e := by
              calc
                (acc * base) * ((base * base) ^ (e / 2)) =
                    (acc * base) * base ^ (2 * (e / 2)) := by rw [square_pow]
                _ = acc * base ^ (2 * (e / 2) + 1) := by
                  rw [show 2 * (e / 2) + 1 = Nat.succ (2 * (e / 2)) by omega]
                  rw [Int.pow_succ, Int.mul_assoc]
                  rw [Int.mul_comm base (base ^ (2 * (e / 2)))]
                _ = acc * base ^ e :=
                  congrArg (fun k => acc * base ^ k) he |>.symm
            have heq : Int.ModEq p
                ((acc * base) * ((base * base) ^ (e / 2))) (acc * base ^ e) := by
              rw [halg]
            have h := hrec.trans (hstep.trans heq)
            simpa [modularGo, e, hodd] using h
          · have hzero : e % 2 = 0 := Nat.mod_two_ne_one.mp hodd
            have he : e = 2 * (e / 2) := by omega
            have hrec := ih (e / 2) hlt ((base * base) % p) acc p
            have hstep : Int.ModEq p
                (acc * (((base * base) % p) ^ (e / 2)))
                (acc * ((base * base) ^ (e / 2))) :=
              Int.ModEq.mul (Int.ModEq.refl _)
                (Int.ModEq.pow _ (Int.mod_modEq _ _))
            have halg : acc * ((base * base) ^ (e / 2)) = acc * base ^ e := by
              calc
                acc * ((base * base) ^ (e / 2)) = acc * base ^ (2 * (e / 2)) := by
                  rw [square_pow]
                _ = acc * base ^ e :=
                  congrArg (fun k => acc * base ^ k) he |>.symm
            have heq : Int.ModEq p (acc * ((base * base) ^ (e / 2)))
                (acc * base ^ e) := by
              rw [halg]
            have h := hrec.trans (hstep.trans heq)
            simpa [modularGo, e, hodd] using h

theorem modularPow_correct (x : Int) (n : Nat) (p : Int) (hp : 0 < p) :
    postcondition x n p (modularPow x n p) := by
  have hp0 : p ≠ 0 := by omega
  have hrange := modularGo_range hp n (x % p) ((1 : Int) % p)
    (Int.emod_nonneg _ hp0) (Int.emod_lt_of_pos _ hp)
  have hgo := modularGo_modEq n (x % p) ((1 : Int) % p) p
  have htarget : Int.ModEq p (((1 : Int) % p) * (x % p) ^ n) (x ^ n) := by
    have hmul := Int.ModEq.mul (Int.mod_modEq (1 : Int) p)
      (Int.ModEq.pow n (Int.mod_modEq x p))
    simpa using hmul
  exact ⟨hrange.1, hrange.2, hgo.trans htarget⟩

prove_correct powMod by
  velvet_vcgen [powMod, postcondition]
  case continuation => simp [modularPow]
  case powered =>
    subst exp
    simp [modularGo] at continuation
    rw [continuation]
    exact modularPow_correct _ _ _ positive_modulus
  case exponent => omega
  case continuation =>
    cases exp with
    | zero => contradiction
    | succ exp' => simpa [modularGo, odd] using continuation
  case exponent => omega
  case continuation =>
    cases exp with
    | zero => contradiction
    | succ exp' => simpa [modularGo, odd] using continuation
  case continuation => exact continuation
  case finished => omega

end Proof

end PowXN
