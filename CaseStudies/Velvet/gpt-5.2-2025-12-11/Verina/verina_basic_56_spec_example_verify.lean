import Lean
import Mathlib.Tactic

set_option maxHeartbeats 1000000






def precondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat) : Prop :=
  sStart + len ≤ src.size ∧ dStart + len ≤ dest.size

def postcondition (src : Array Int) (sStart : Nat) (dest : Array Int) (dStart : Nat) (len : Nat)
    (result : Array Int) : Prop :=
  result.size = dest.size ∧
  (∀ j : Nat, j < dest.size →
    (if h : (dStart ≤ j ∧ j < dStart + len) then
      result[j]! = src[sStart + (j - dStart)]!
    else
      result[j]! = dest[j]!))


def test1_src : Array Int := #[10, 20, 30, 40, 50]

def test1_sStart : Nat := 1

def test1_dest : Array Int := #[1, 2, 3, 4, 5, 6]

def test1_dStart : Nat := 3

def test1_len : Nat := 2

def test1_Expected : Array Int := #[1, 2, 3, 20, 30, 6]

def test3_src : Array Int := #[100, 200]

def test3_sStart : Nat := 0

def test3_dest : Array Int := #[1, 2, 3]

def test3_dStart : Nat := 1

def test3_len : Nat := 0

def test3_Expected : Array Int := #[1, 2, 3]

def test7_src : Array Int := #[11, 12, 13, 14]

def test7_sStart : Nat := 1

def test7_dest : Array Int := #[0, 1, 2, 3, 4]

def test7_dStart : Nat := 0

def test7_len : Nat := 3

def test7_Expected : Array Int := #[12, 13, 14, 3, 4]







section Proof
theorem test1_precondition :
    precondition test1_src test1_sStart test1_dest test1_dStart test1_len := by
  unfold precondition
  simp [test1_src, test1_sStart, test1_dest, test1_dStart, test1_len]

theorem test1_postcondition :
    postcondition test1_src test1_sStart test1_dest test1_dStart test1_len test1_Expected := by
  unfold postcondition
  constructor
  · simp [test1_Expected, test1_dest]
  · intro j hj
    -- dest.size = 6, so j ∈ {0,1,2,3,4,5}
    have hj' : j < 6 := by simpa [test1_dest] using hj
    interval_cases j <;>
      simp [test1_src, test1_sStart, test1_dest, test1_dStart, test1_len, test1_Expected]

theorem test3_precondition : precondition test3_src test3_sStart test3_dest test3_dStart test3_len := by
  unfold precondition
  simp [test3_src, test3_sStart, test3_dest, test3_dStart, test3_len]

theorem test3_postcondition :
    postcondition test3_src test3_sStart test3_dest test3_dStart test3_len test3_Expected := by
  unfold postcondition
  constructor
  · simp [test3_Expected, test3_dest]
  · intro j hj
    have hfalse : ¬(test3_dStart ≤ j ∧ j < test3_dStart + test3_len) := by
      intro h
      have hlt : j < test3_dStart := by
        simpa [test3_dStart, test3_len, Nat.add_zero] using h.2
      exact (Nat.not_lt_of_ge h.1) hlt
    simp [hfalse, test3_Expected, test3_dest]

theorem test7_precondition : precondition test7_src test7_sStart test7_dest test7_dStart test7_len := by
  unfold precondition
  constructor
  · decide
  · decide

theorem test7_postcondition :
    postcondition test7_src test7_sStart test7_dest test7_dStart test7_len test7_Expected := by
  unfold postcondition
  constructor
  · decide
  · intro j hj
    -- rewrite concrete parameters
    simp [test7_src, test7_sStart, test7_dest, test7_dStart, test7_len, test7_Expected] at hj ⊢
    -- now hj : j < 5
    interval_cases j <;> simp [Nat.succ_lt_succ_iff]

theorem uniqueness
    (src : Array Int)
    (sStart : Nat)
    (dest : Array Int)
    (dStart : Nat)
    (len : Nat)
    : precondition src sStart dest dStart len →
  (∀ ret1 ret2,
    postcondition src sStart dest dStart len ret1 →
    postcondition src sStart dest dStart len ret2 →
    ret1 = ret2) := by
  intro _hpre
  intro ret1 ret2 hpost1 hpost2
  rcases hpost1 with ⟨hsz1, hspec1⟩
  rcases hpost2 with ⟨hsz2, hspec2⟩
  apply Array.ext
  · -- sizes
    simpa [hsz1, hsz2]
  · intro i hi1 hi2
    have hid : i < dest.size := by
      simpa [hsz1] using hi1
    classical
    by_cases hseg : (dStart ≤ i ∧ i < dStart + len)
    · have h1 := hspec1 i hid
      have h2 := hspec2 i hid
      simp [hseg] at h1 h2
      -- Array.ext expects equality of `get` (with proofs), not `get!`
      have : ret1[i] = ret2[i] := by
        -- rewrite `get` to `get!` using the in-bounds proofs, then close by `h1/h2`
        simpa [Array.get, hi1, hi2] using (h1.trans h2.symm)
      exact this
    · have h1 := hspec1 i hid
      have h2 := hspec2 i hid
      simp [hseg] at h1 h2
      have : ret1[i] = ret2[i] := by
        simpa [Array.get, hi1, hi2] using (h1.trans h2.symm)
      exact this
end Proof
