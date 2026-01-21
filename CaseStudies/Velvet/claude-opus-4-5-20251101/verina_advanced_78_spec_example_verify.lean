import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000





def hasSolution (nums : List Int) (target : Int) : Prop :=
  ∃ i j : Nat, i < j ∧ j < nums.length ∧ nums[i]! + nums[j]! = target

def precondition (nums : List Int) (target : Int) : Prop :=
  hasSolution nums target



def ensures1 (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  result.1 < result.2


def ensures2 (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  result.2 < nums.length


def ensures3 (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  nums[result.1]! + nums[result.2]! = target

def postcondition (nums : List Int) (target : Int) (result : Prod Nat Nat) : Prop :=
  ensures1 nums target result ∧
  ensures2 nums target result ∧
  ensures3 nums target result


def test1_nums : List Int := [2, 7, 11, 15]

def test1_target : Int := 9

def test1_Expected : Prod Nat Nat := (0, 1)

def test3_nums : List Int := [3, 3]

def test3_target : Int := 6

def test3_Expected : Prod Nat Nat := (0, 1)

def test5_nums : List Int := [0, 4, 3, 0]

def test5_target : Int := 0

def test5_Expected : Prod Nat Nat := (0, 3)







section Proof
theorem test1_precondition :
  precondition test1_nums test1_target := by
  unfold precondition hasSolution test1_nums test1_target
  use 0, 1
  native_decide

theorem test1_postcondition :
  postcondition test1_nums test1_target test1_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 test1_nums test1_target test1_Expected
  native_decide

theorem test3_precondition :
  precondition test3_nums test3_target := by
  unfold precondition hasSolution test3_nums test3_target
  use 0, 1
  native_decide

theorem test3_postcondition :
  postcondition test3_nums test3_target test3_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 test3_nums test3_target test3_Expected
  native_decide

theorem test5_precondition : precondition test5_nums test5_target := by
  unfold precondition hasSolution test5_nums test5_target
  use 0, 3
  native_decide

theorem test5_postcondition :
  postcondition test5_nums test5_target test5_Expected := by
  unfold postcondition ensures1 ensures2 ensures3 test5_nums test5_target test5_Expected
  native_decide
end Proof
