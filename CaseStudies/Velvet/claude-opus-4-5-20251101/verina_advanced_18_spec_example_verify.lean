import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def numDigits (n : Nat) : Nat :=
  if n < 10 then 1 else 1 + numDigits (n / 10)


def digitAt (n : Nat) (i : Nat) : Nat :=
  (n / (10 ^ i)) % 10


def armstrongSumAux (n : Nat) (k : Nat) (i : Nat) : Nat :=
  if i = 0 then 0
  else armstrongSumAux n k (i - 1) + (digitAt n (i - 1)) ^ k

def armstrongSum (n : Nat) : Nat :=
  let k := numDigits n
  armstrongSumAux n k k

def precondition (n : Nat) : Prop :=
  True

def postcondition (n : Nat) (result : Bool) : Prop :=
  result = true ↔ armstrongSum n = n


def test3_n : Nat := 10

def test3_Expected : Bool := false

def test4_n : Nat := 153

def test4_Expected : Bool := true

def test5_n : Nat := 9474

def test5_Expected : Bool := true

def test3_n : Nat := 10

def test3_Expected : Bool := false

def test4_n : Nat := 153

def test4_Expected : Bool := true







section Proof
end Proof