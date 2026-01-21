import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def arraySorted (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!


def arrayPerm (a : Array Int) (b : Array Int) : Prop :=
  a.toList.Perm b.toList



def precondition (a : Array Int) : Prop :=
  True

def postcondition (a : Array Int) (result : Array Int) : Prop :=
  result.size = a.size ∧
  arraySorted result ∧
  arrayPerm a result


def test1_a : Array Int := #[5, 4, 3, 2, 1]

def test1_Expected : Array Int := #[1, 2, 3, 4, 5]

def test3_a : Array Int := #[3, 1, 2, 1, 5]

def test3_Expected : Array Int := #[1, 1, 2, 3, 5]

def test7_a : Array Int := #[-2, 0, 5, -1]

def test7_Expected : Array Int := #[-2, -1, 0, 5]







section Proof
theorem test1_precondition : precondition test1_a := by
    intros; expose_names; exact (trivial); done

theorem test1_postcondition : postcondition test1_a test1_Expected := by
  unfold postcondition
  constructor
  · simp [test1_a, test1_Expected]
  · constructor
    · -- arraySorted test1_Expected
      unfold arraySorted
      intro i j hij hj
      have hj' : j < 5 := by simpa [test1_Expected] using hj
      have hi' : i < 5 := lt_trans hij hj'
      interval_cases i <;> interval_cases j <;> simp [test1_Expected] at hij hj' ⊢
    · -- arrayPerm test1_a test1_Expected
      unfold arrayPerm
      -- `[5,4,3,2,1]` is the reverse of `[1,2,3,4,5]`
      simpa [test1_a, test1_Expected] using
        (List.reverse_perm ([1, 2, 3, 4, 5] : List Int))

theorem test3_precondition : precondition test3_a := by
    intros; expose_names; exact (trivial); done

theorem test3_postcondition : postcondition test3_a test3_Expected := by
  unfold postcondition
  constructor
  · have hsize : test3_Expected.size = test3_a.size := by
      simp [test3_a, test3_Expected]
    exact hsize
  · constructor
    · have hsorted : arraySorted test3_Expected := by
        unfold arraySorted
        intro i j hij hj
        have hj' : j < 5 := by simpa [test3_Expected] using hj
        have hi' : i < 5 := lt_trans hij hj'
        interval_cases i <;> interval_cases j <;> simp [test3_Expected] at hij hj' ⊢
      exact hsorted
    · have hperm : arrayPerm test3_a test3_Expected := by
        unfold arrayPerm
        -- both sides are concrete lists; `simp` reduces `toList` and the permutation can be shown by swaps/trans
        -- (a concrete proof can be filled using `List.Perm.swap` / `List.Perm.trans` or `List.perm_iff_count`)
        -- here we just structure the goal into the intended lemma application.
        have hperm_lists : (test3_a.toList).Perm (test3_Expected.toList) := by
          -- one possible approach:
          --   simpa [test3_a, test3_Expected] using (by
          --     -- build permutation by swaps/trans
          --     ...)
          (try simp at *; expose_names); exact List.isPerm_iff.mp rfl; done
        simpa using hperm_lists
      exact hperm

theorem test7_precondition : precondition test7_a := by
    intros; expose_names; exact (trivial); done

theorem test7_postcondition : postcondition test7_a test7_Expected := by
  unfold postcondition
  constructor
  · have hsize : test7_Expected.size = test7_a.size := by
      simp [test7_a, test7_Expected]
    exact hsize
  · constructor
    · have hsorted : arraySorted test7_Expected := by
        unfold arraySorted
        intro i j hij hj
        have hj' : j < 4 := by simpa [test7_Expected] using hj
        have hi' : i < 4 := by exact lt_trans hij hj'
        interval_cases i <;> interval_cases j <;> simp [test7_Expected] at hij hj' ⊢
      exact hsorted
    · have hperm : arrayPerm test7_a test7_Expected := by
        unfold arrayPerm
        have hperm_concrete : ([-2, (0 : Int), 5, -1] : List Int).Perm ([-2, -1, 0, 5] : List Int) := by
          have hswap1 : ([-2, (0 : Int), 5, -1] : List Int).Perm ([-2, (0 : Int), -1, 5] : List Int) := by
            -- swap 5 and -1 inside the tail, then cons -2
            (try simp at *; expose_names); exact List.Perm.swap (-1) 5 []; done
          have hswap2 : ([-2, (0 : Int), -1, 5] : List Int).Perm ([-2, -1, 0, 5] : List Int) := by
            -- swap 0 and -1 inside the tail, then cons -2
            (try simp at *; expose_names); exact List.Perm.swap (-1) 0 [5]; done
          have htrans : ([-2, (0 : Int), 5, -1] : List Int).Perm ([-2, -1, 0, 5] : List Int) := by
            exact List.Perm.trans hswap1 hswap2
          exact htrans
        have hperm_lists : test7_a.toList.Perm test7_Expected.toList := by
          simpa [test7_a, test7_Expected] using hperm_concrete
        exact hperm_lists
      exact hperm

theorem uniqueness
    (a : Array Int)
    : precondition a →
  (∀ ret1 ret2,
    postcondition a ret1 →
    postcondition a ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  rcases hpost1 with ⟨_hsize1, hsorted1, hperm1⟩
  rcases hpost2 with ⟨_hsize2, hsorted2, hperm2⟩

  -- from permutations with `a`, get permutation between the results
  have hperm12 : ret1.toList.Perm ret2.toList := by
    simpa [arrayPerm] using hperm1.symm.trans hperm2

  classical

  -- show the underlying lists are equal using `Perm.eq_of_sorted`
  have hlistEq : ret1.toList = ret2.toList := by
    -- `arraySorted` implies `Pairwise (≤)` on the underlying list
    have hpair1 : ret1.toList.Pairwise (fun x y : Int => x ≤ y) := by
      rw [List.pairwise_iff_get]
      intro i j hij
      have hj' : (j : Nat) < ret1.size := by
        -- `j.isLt : (j : Nat) < ret1.toList.length`
        -- rewrite `ret1.size` as `ret1.toList.length`
        simpa [Array.length_toList] using (j.isLt)
      have hij' : (i : Nat) < (j : Nat) := hij
      -- bridge list `get` to array indexing
      simpa using (hsorted1 (i : Nat) (j : Nat) hij' hj')

    have hpair2 : ret2.toList.Pairwise (fun x y : Int => x ≤ y) := by
      rw [List.pairwise_iff_get]
      intro i j hij
      have hj' : (j : Nat) < ret2.size := by
        simpa [Array.length_toList] using (j.isLt)
      have hij' : (i : Nat) < (j : Nat) := hij
      simpa using (hsorted2 (i : Nat) (j : Nat) hij' hj')

    have want :
        ∀ x y : Int,
          x ∈ ret1.toList → y ∈ ret2.toList → x ≤ y → y ≤ x → x = y := by
      intro x y _hx _hy hxy hyx
      exact le_antisymm hxy hyx

    exact
      List.Perm.eq_of_sorted
        (l₁ := ret1.toList)
        (l₂ := ret2.toList)
        want
        hpair1
        hpair2
        hperm12

  -- arrays are equal if their `toList`s are equal
  exact Array.ext' hlistEq
end Proof
