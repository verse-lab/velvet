import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000



def cube (x : Int) : Int := x * x * x



def precondition (a : Array Int) : Prop :=
  True



def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  ∀ i : Nat, i < a.size → result[i]! = cube a[i]!


def test1_a : Array Int := #[1, 2, 3, 4]

def test1_Expected : Array Int := #[1, 8, 27, 64]

def test2_a : Array Int := #[0, -1, -2, 3]

def test2_Expected : Array Int := #[0, -1, -8, 27]

def test3_a : Array Int := #[]

def test3_Expected : Array Int := #[]







section Proof
theorem test1_precondition :
  precondition test1_a := by
  intros; expose_names; exact (trivial); done

theorem test1_postcondition :
  postcondition test1_a test1_Expected := by
  simp only [postcondition, test1_a, test1_Expected, cube]
  constructor
  · rfl
  · intro i hi
    simp only [Array.size_toArray, List.length_cons, List.length_nil] at hi
    match i with
    | 0 | 1 | 2 | 3 => native_decide
    | n + 4 => omega

theorem test2_precondition :
  precondition test2_a := by
  intros; expose_names; exact (trivial); done

theorem test2_postcondition :
  postcondition test2_a test2_Expected := by
  simp only [postcondition, test2_a, test2_Expected, cube]
  constructor
  · rfl
  · intro i hi
    simp only [Array.size_toArray, List.length_cons, List.length_nil] at hi
    match i with
    | 0 | 1 | 2 | 3 => native_decide
    | n + 4 => omega

theorem test3_precondition :
  precondition test3_a := by
  intros; expose_names; exact (trivial); done

theorem test3_postcondition :
  postcondition test3_a test3_Expected := by
  unfold postcondition test3_a test3_Expected
  constructor
  · rfl
  · intro i hi
    simp only [Array.size_empty] at hi
    exact absurd hi (Nat.not_lt_zero i)

theorem uniqueness_0
    (a : Array ℤ)
    (hpre : precondition a)
    (ret1 : Array ℤ)
    (ret2 : Array ℤ)
    (hpost1 : postcondition a ret1)
    (hpost2 : postcondition a ret2)
    : ret1.size = a.size := by
    exact hpost1.1

theorem uniqueness_1
    (a : Array ℤ)
    (hpre : precondition a)
    (ret1 : Array ℤ)
    (ret2 : Array ℤ)
    (hpost1 : postcondition a ret1)
    (hpost2 : postcondition a ret2)
    (hsize1 : ret1.size = a.size)
    : ∀ i < a.size, ret1[i]! = cube a[i]! := by
    exact hpost1.2

theorem uniqueness_2
    (a : Array ℤ)
    (hpre : precondition a)
    (ret1 : Array ℤ)
    (ret2 : Array ℤ)
    (hpost1 : postcondition a ret1)
    (hpost2 : postcondition a ret2)
    (hsize1 : ret1.size = a.size)
    (helem1 : ∀ i < a.size, ret1[i]! = cube a[i]!)
    : ret2.size = a.size := by
    intros; expose_names; exact (uniqueness_0 a hpre ret2 ret1 hpost2 hpost1); done

theorem uniqueness_3
    (a : Array ℤ)
    (hpre : precondition a)
    (ret1 : Array ℤ)
    (ret2 : Array ℤ)
    (hpost1 : postcondition a ret1)
    (hpost2 : postcondition a ret2)
    (hsize1 : ret1.size = a.size)
    (helem1 : ∀ i < a.size, ret1[i]! = cube a[i]!)
    (hsize2 : ret2.size = a.size)
    : ∀ i < a.size, ret2[i]! = cube a[i]! := by
    intros; expose_names; exact (uniqueness_1 a hpre ret2 ret1 hpost2 hpost1 hsize2 i h); done

theorem uniqueness_4
    (a : Array ℤ)
    (hpre : precondition a)
    (ret1 : Array ℤ)
    (ret2 : Array ℤ)
    (hpost1 : postcondition a ret1)
    (hpost2 : postcondition a ret2)
    (hsize1 : ret1.size = a.size)
    (helem1 : ∀ i < a.size, ret1[i]! = cube a[i]!)
    (hsize2 : ret2.size = a.size)
    (helem2 : ∀ i < a.size, ret2[i]! = cube a[i]!)
    : ret1.size = ret2.size := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness_5
    (a : Array ℤ)
    (hpre : precondition a)
    (ret1 : Array ℤ)
    (ret2 : Array ℤ)
    (hpost1 : postcondition a ret1)
    (hpost2 : postcondition a ret2)
    (hsize1 : ret1.size = a.size)
    (helem1 : ∀ i < a.size, ret1[i]! = cube a[i]!)
    (hsize2 : ret2.size = a.size)
    (helem2 : ∀ i < a.size, ret2[i]! = cube a[i]!)
    (hsize_eq : ret1.size = ret2.size)
    (i : ℕ)
    (hi1 : i < ret1.size)
    (hi2 : i < ret2.size)
    (hi_a : i < a.size)
    (hret1_cube : ret1[i]! = cube a[i]!)
    (hret2_cube : ret2[i]! = cube a[i]!)
    : ret1[i]! = ret2[i]! := by
    intros; expose_names ; (first | grind | (simp at * ; grind) | (simp_all; grind) | rfl | assumption | exact? )

theorem uniqueness (a : Array Int):
  precondition a →
  (∀ ret1 ret2,
    postcondition a ret1 →
    postcondition a ret2 →
    ret1 = ret2) := by
  intro hpre ret1 ret2 hpost1 hpost2
  -- Extract components from postcondition of ret1
  have hsize1 : ret1.size = a.size := by (try simp at *; expose_names); exact (uniqueness_0 a hpre ret1 ret2 hpost1 hpost2); done
  have helem1 : ∀ i : Nat, i < a.size → ret1[i]! = cube a[i]! := by (try simp at *; expose_names); exact (uniqueness_1 a hpre ret1 ret2 hpost1 hpost2 hsize1); done
  -- Extract components from postcondition of ret2
  have hsize2 : ret2.size = a.size := by (try simp at *; expose_names); exact (uniqueness_2 a hpre ret1 ret2 hpost1 hpost2 hsize1 helem1); done
  have helem2 : ∀ i : Nat, i < a.size → ret2[i]! = cube a[i]! := by (try simp at *; expose_names); exact (uniqueness_3 a hpre ret1 ret2 hpost1 hpost2 hsize1 helem1 hsize2); done
  -- Establish size equality between ret1 and ret2
  have hsize_eq : ret1.size = ret2.size := by (try simp at *; expose_names); exact (uniqueness_4 a hpre ret1 ret2 hpost1 hpost2 hsize1 helem1 hsize2 helem2); done
  -- Apply Array.ext to prove equality
  apply Array.ext hsize_eq
  intro i hi1 hi2
  -- For valid index i, show ret1[i] = ret2[i]
  have hi_a : i < a.size := by (try simp at *; expose_names); exact (Nat.lt_of_lt_of_eq hi1 hsize1); done
  -- Get that ret1[i]! = cube a[i]!
  have hret1_cube : ret1[i]! = cube a[i]! := by (try simp at *; expose_names); exact (helem1 i hi_a); done
  -- Get that ret2[i]! = cube a[i]!
  have hret2_cube : ret2[i]! = cube a[i]! := by (try simp at *; expose_names); exact (helem2 i hi_a); done
  -- Show ret1[i]! = ret2[i]! by transitivity
  have heq_bang : ret1[i]! = ret2[i]! := by (try simp at *; expose_names); exact (uniqueness_5 a hpre ret1 ret2 hpost1 hpost2 hsize1 helem1 hsize2 helem2 hsize_eq i hi1 hi2 hi_a hret1_cube hret2_cube); done
  -- Connect getElem! to getElem for valid indices
  have hret1_conv : ret1[i]! = ret1[i] := by (try simp at *; expose_names); exact (getElem!_pos ret1 i hi1); done
  have hret2_conv : ret2[i]! = ret2[i] := by (try simp at *; expose_names); exact (getElem!_pos ret2 i hi2); done
  -- Conclude ret1[i] = ret2[i]
  calc ret1[i] = ret1[i]! := by (try simp at *; expose_names); exact id (Eq.symm hret1_conv); done
    _ = ret2[i]! := heq_bang
    _ = ret2[i] := hret2_conv
end Proof
