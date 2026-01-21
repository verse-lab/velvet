import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000




def isSortedNondecreasing (a : Array Int) : Prop :=
  ∀ (i : Nat) (j : Nat), i < j → j < a.size → a[i]! ≤ a[j]!


def isLowerBoundIndex (a : Array Int) (key : Int) (idx : Nat) : Prop :=
  idx ≤ a.size ∧
  (∀ (i : Nat), i < idx → a[i]! < key) ∧
  (∀ (i : Nat), idx ≤ i → i < a.size → key ≤ a[i]!)



def precondition (a : Array Int) (key : Int) : Prop :=
  isSortedNondecreasing a



def postcondition (a : Array Int) (key : Int) (result : Nat) : Prop :=
  isLowerBoundIndex a key result


def test1_a : Array Int := #[1, 3, 5, 7, 9]

def test1_key : Int := 5

def test1_Expected : Nat := 2

def test2_a : Array Int := #[1, 3, 5, 7, 9]

def test2_key : Int := 6

def test2_Expected : Nat := 3

def test5_a : Array Int := #[1, 1, 1, 1]

def test5_key : Int := 1

def test5_Expected : Nat := 0







section Proof
theorem test1_precondition : precondition test1_a test1_key := by
  unfold precondition
  unfold isSortedNondecreasing
  intro i j hij hj
  -- reduce the bound `j < test1_a.size` to `j < 5`
  have hj' : j < 5 := by simpa [test1_a] using hj
  -- enumerate all possibilities for `j < 5`
  have hjCases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
    omega
  rcases hjCases with rfl | rfl | rfl | rfl | rfl
  · -- j = 0: impossible since i < 0
    cases (Nat.not_lt_zero i hij)
  · -- j = 1: i = 0
    have hi : i = 0 := by omega
    subst hi
    simp [test1_a]
  · -- j = 2: i = 0 or 1
    have hiCases : i = 0 ∨ i = 1 := by omega
    rcases hiCases with rfl | rfl <;> simp [test1_a]
  · -- j = 3: i = 0, 1, or 2
    have hiCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hiCases with rfl | rfl | rfl <;> simp [test1_a]
  · -- j = 4: i = 0, 1, 2, or 3
    have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hiCases with rfl | rfl | rfl | rfl <;> simp [test1_a]

theorem test1_postcondition : postcondition test1_a test1_key test1_Expected := by
  unfold postcondition
  change isLowerBoundIndex test1_a test1_key test1_Expected
  unfold isLowerBoundIndex
  refine And.intro ?h₁ (And.intro ?h₂ ?h₃)

  · have h_size : (2 : Nat) ≤ test1_a.size := by (try simp at *; expose_names); exact (Nat.le_of_ble_eq_true rfl); done
    have h₁ : test1_Expected ≤ test1_a.size := by simpa [test1_Expected] using h_size
    exact h₁

  · have h₂ : ∀ i : Nat, i < test1_Expected → test1_a[i]! < test1_key := by
      intro i hi
      have hi' : i < 2 := by simpa [test1_Expected] using hi
      have hiCases : i = 0 ∨ i = 1 := by omega
      rcases hiCases with rfl | rfl
      · simp [test1_a, test1_key]
      · simp [test1_a, test1_key]
    exact h₂

  · have h₃ : ∀ i : Nat, test1_Expected ≤ i → i < test1_a.size → test1_key ≤ test1_a[i]! := by
      intro i hge hlt
      have hge' : 2 ≤ i := by simpa [test1_Expected] using hge
      have hlt' : i < 5 := by simpa [test1_a] using hlt
      have hiCases : i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hiCases with rfl | rfl | rfl
      · simp [test1_a, test1_key]
      · simp [test1_a, test1_key]
      · simp [test1_a, test1_key]
    exact h₃

theorem test2_precondition : precondition test2_a test2_key := by
  -- precondition ignores the key; it is just sortedness of the array
  simp [precondition, isSortedNondecreasing]
  intro i j hij hj
  -- `simp [test2_a]` can evaluate `size` and all `!`-indexing on this literal array
  have hj' : j < 5 := by simpa [test2_a] using hj
  -- split into the finitely many cases for `j < 5`
  have hjCases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
    omega
  rcases hjCases with rfl | rfl | rfl | rfl | rfl
  · -- j = 0 is impossible since i < 0
    exact (Nat.not_lt_zero _ hij).elim
  · -- j = 1, so i = 0
    have hi : i = 0 := by omega
    subst hi
    simp [test2_a]
  · -- j = 2, so i = 0 or 1
    have hiCases : i = 0 ∨ i = 1 := by omega
    rcases hiCases with rfl | rfl
    · simp [test2_a]
    · simp [test2_a]
  · -- j = 3, so i = 0 or 1 or 2
    have hiCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hiCases with rfl | rfl | rfl
    · simp [test2_a]
    · simp [test2_a]
    · simp [test2_a]
  · -- j = 4, so i = 0 or 1 or 2 or 3
    have hiCases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hiCases with rfl | rfl | rfl | rfl
    · simp [test2_a]
    · simp [test2_a]
    · simp [test2_a]
    · simp [test2_a]

theorem test2_postcondition : postcondition test2_a test2_key test2_Expected := by
  unfold postcondition isLowerBoundIndex
  constructor
  · -- idx ≤ a.size
    simp [test2_Expected, test2_a]
  constructor
  · -- ∀ i, i < idx → a[i]! < key
    intro i hi
    have hi' : i < 3 := by simpa [test2_Expected] using hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by
      omega
    rcases hcases with rfl | rfl | rfl <;> simp [test2_a, test2_key]
  · -- ∀ i, idx ≤ i → i < a.size → key ≤ a[i]!
    intro i hge hlt
    have hge' : 3 ≤ i := by simpa [test2_Expected] using hge
    have hlt' : i < 5 := by simpa [test2_a] using hlt
    have hcases : i = 3 ∨ i = 4 := by
      omega
    rcases hcases with rfl | rfl <;> simp [test2_a, test2_key]

theorem test5_precondition : precondition test5_a test5_key := by
  -- Step 1: unfold the precondition (key is irrelevant)
  unfold precondition
  -- Step 2: unfold sortedness definition
  unfold isSortedNondecreasing
  intro i j hij hj

  -- Step 3: compute the size of the concrete array
  have hj' : j < 4 := by
    simpa [test5_a] using hj

  -- Step 4: enumerate the possible values of `j` (since `j < 4`)
  have hjCases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
    omega

  -- Step 5: finish by concrete computation in each case
  rcases hjCases with rfl | rfl | rfl | rfl
  · -- j = 0 contradicts i < 0
    cases (Nat.not_lt_zero i hij)
  · -- j = 1, so i = 0
    have hi : i = 0 := by omega
    subst hi
    simp [test5_a]
  · -- j = 2, so i = 0 or 1
    have hiCases : i = 0 ∨ i = 1 := by omega
    rcases hiCases with rfl | rfl <;> simp [test5_a]
  · -- j = 3, so i = 0 or 1 or 2
    have hiCases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hiCases with rfl | rfl | rfl <;> simp [test5_a]

theorem test5_postcondition : postcondition test5_a test5_key test5_Expected := by
  unfold postcondition
  unfold isLowerBoundIndex
  constructor
  · -- idx ≤ a.size
    simp [test5_Expected, test5_a]
  · constructor
    · -- ∀ i, i < idx → a[i]! < key  (vacuous since idx = 0)
      intro i hi
      exfalso
      exact (Nat.not_lt_zero i) hi
    · -- ∀ i, idx ≤ i → i < a.size → key ≤ a[i]!
      intro i _ hi
      -- simplify size and bounds
      have hi4 : i < 4 := by simpa [test5_a] using hi
      -- compute the element by cases on i < 4
      have hget : test5_a[i]! = (1 : Int) := by
        cases i with
        | zero =>
            simp [test5_a]
        | succ i =>
            cases i with
            | zero =>
                simp [test5_a]
            | succ i =>
                cases i with
                | zero =>
                    simp [test5_a]
                | succ i =>
                    cases i with
                    | zero =>
                        simp [test5_a]
                    | succ i =>
                        -- impossible since i.succ.succ.succ.succ < 4
                        exfalso
                        omega
      -- conclude key ≤ a[i]!
      simpa [test5_key, hget] using (Int.le_refl (1 : Int))

theorem uniqueness
    (a : Array Int)
    (key : Int)
    : precondition a key →
  (∀ ret1 ret2,
    postcondition a key ret1 →
    postcondition a key ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  -- unfold postcondition/isLowerBoundIndex structure
  rcases hpost1 with ⟨h1_le_size, h1_lt, h1_ge⟩
  rcases hpost2 with ⟨h2_le_size, h2_lt, h2_ge⟩
  apply Nat.le_antisymm
  · -- ret1 ≤ ret2
    by_contra hnot
    have hlt : ret2 < ret1 := Nat.lt_of_not_ge hnot
    -- from ret2 < ret1, ret2 is in the "strictly before ret1" region
    have h_a_ret2_lt_key : a[ret2]! < key := h1_lt ret2 hlt
    -- show ret2 < a.size (otherwise ret1 ≤ a.size would be contradicted)
    have hret2_lt_size : ret2 < a.size := by
      have : ret2 < a.size := Nat.lt_of_lt_of_le hlt h1_le_size
      exact this
    -- from ret2 being a lower bound index, at i = ret2 we have key ≤ a[ret2]!
    have h_key_le_a_ret2 : key ≤ a[ret2]! := h2_ge ret2 (Nat.le_refl _) hret2_lt_size
    -- contradiction on Int order
    exact (Lean.Omega.Int.lt_le_asymm h_a_ret2_lt_key h_key_le_a_ret2)
  · -- ret2 ≤ ret1
    by_contra hnot
    have hlt : ret1 < ret2 := Nat.lt_of_not_ge hnot
    have h_a_ret1_lt_key : a[ret1]! < key := h2_lt ret1 hlt
    have hret1_lt_size : ret1 < a.size := by
      exact Nat.lt_of_lt_of_le hlt h2_le_size
    have h_key_le_a_ret1 : key ≤ a[ret1]! := h1_ge ret1 (Nat.le_refl _) hret1_lt_size
    exact (Lean.Omega.Int.lt_le_asymm h_a_ret1_lt_key h_key_le_a_ret1)
end Proof
