import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil
import CaseStudies.Velvet.SpecDSL

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

/- Problem Description
    MinCostPath: Find minimum cost path from (0,0) to (m,n) in a cost matrix
    Natural language breakdown:
    1. We have a 2D cost matrix where each cell contains a non-negative cost value
    2. We start at position (0, 0) and want to reach position (m, n)
    3. MOVEMENT CONSTRAINT: From any cell (i, j), we can move to three possible cells:
       - Right: (i, j+1)
       - Down: (i+1, j)
       - Diagonal down-right: (i+1, j+1)
       This allows for more flexible pathfinding while maintaining forward progress
    4. The cost of a path is the sum of all costs of cells visited along the path
    5. We want to find the minimum possible total cost among all valid paths
    6. The function should return this minimum cost
    7. Edge cases:
       - Single cell (m=0, n=0): cost is just that cell's value
       - First row or column only: must follow that edge
       - Diagonal moves can provide shortcuts and reduce total cost
-/

specdef MinCostPathSpec

-- Helper Functions

-- Helper definition for valid path (right, down, and diagonal moves allowed)
def isValidPath (path: List (Nat × Nat)) (startRow startCol endRow endCol: Nat) : Prop :=
  path.length > 0 ∧
  path.head? = some (startRow, startCol) ∧
  path.getLast? = some (endRow, endCol) ∧
  ∀ i, i + 1 < path.length →
    let curr := path[i]!
    let next := path[i + 1]!
    (next.1 = curr.1 ∧ next.2 = curr.2 + 1) ∨      -- right move
    (next.1 = curr.1 + 1 ∧ next.2 = curr.2) ∨      -- down move
    (next.1 = curr.1 + 1 ∧ next.2 = curr.2 + 1)    -- diagonal down-right move

-- Helper definition for path cost calculation
def pathCost (cost: Array (Array Nat)) (path: List (Nat × Nat)) : Nat :=
  path.foldl (fun acc (i, j) =>
    acc + (cost[i]!)[j]!) 0

def require1 (cost: Array (Array Nat)) (m: Nat) (n: Nat) :=
  cost.size > 0
def require2 (cost: Array (Array Nat)) (m: Nat) (n: Nat) :=
  ∀ i < cost.size, cost[i]!.size > 0
def require3 (cost: Array (Array Nat)) (m: Nat) (n: Nat) :=
  ∀ i < cost.size, cost[i]!.size = cost[0]!.size
def require4 (cost: Array (Array Nat)) (m: Nat) (n: Nat) :=
  m < cost.size
def require5 (cost: Array (Array Nat)) (m: Nat) (n: Nat) :=
  n < cost[0]!.size
def ensures1 (cost: Array (Array Nat)) (m: Nat) (n: Nat) (minCost: Nat) :=
  ∃ path, isValidPath path 0 0 m n ∧ pathCost cost path = minCost  -- achievable minimum
def ensures2 (cost: Array (Array Nat)) (m: Nat) (n: Nat) (minCost: Nat) :=
  ∀ path, isValidPath path 0 0 m n → pathCost cost path ≥ minCost  -- truly minimum
def ensures3 (cost: Array (Array Nat)) (m: Nat) (n: Nat) (minCost: Nat) :=
  (m = 0 ∧ n = 0) → minCost = (cost[0]!)[0]!  -- edge case: start equals end
def_pre (cost: Array (Array Nat)) (m: Nat) (n: Nat) :=
  require1 cost m n ∧
  require2 cost m n ∧
  require3 cost m n ∧
  require4 cost m n ∧
  require5 cost m n
def_post (cost: Array (Array Nat)) (m: Nat) (n: Nat) (minCost: Nat) :=
  ensures1 cost m n minCost ∧
  ensures2 cost m n minCost ∧
  ensures3 cost m n minCost

specend MinCostPathSpec

method MinCostPath (cost: Array (Array Nat)) (m: Nat) (n: Nat)
  return (minCost: Nat)
  require MinCostPathSpec.pre cost m n
  ensures MinCostPathSpec.post cost m n minCost
  do
  pure 0  -- placeholder body for type checking

prove_correct MinCostPath by sorry

section TestCases

-- Test case 1: Example from problem statement (with diagonal moves)
-- cost = [[1, 2, 3], [4, 8, 2], [1, 5, 3]]
-- With diagonal moves allowed, optimal path: (0,0) → (1,1) → (2,2)
-- Cost: 1 + 8 + 3 = 12
-- (Without diagonals it was: (0,0) → (0,1) → (0,2) → (1,2) → (2,2) with cost 11)
-- Actually, let me recalculate:
-- Path (0,0) → (0,1) → (1,2) → (2,2): 1 + 2 + 2 + 3 = 8
-- Path (0,0) → (1,1) → (2,2): 1 + 8 + 3 = 12
-- Path (0,0) → (1,0) → (2,1) → (2,2): 1 + 4 + 5 + 3 = 13
-- Path (0,0) → (0,1) → (0,2) → (1,2) → (2,2): 1 + 2 + 3 + 2 + 3 = 11
-- Path (0,0) → (1,1) → (1,2) → (2,2): 1 + 8 + 2 + 3 = 14
-- The optimal with diagonals is still: (0,0) → (0,1) → (1,2) → (2,2) with cost 8
def test1_cost : Array (Array Nat) := #[#[1, 2, 3], #[4, 8, 2], #[1, 5, 3]]
def test1_m : Nat := 2
def test1_n : Nat := 2
def test1_Expected : Nat := 8

-- Test case 2: Single cell matrix (edge case: start equals end)
-- cost = [[5]]
-- Expected minimum path: (0,0) with cost 5
def test2_cost : Array (Array Nat) := #[#[5]]
def test2_m : Nat := 0
def test2_n : Nat := 0
def test2_Expected : Nat := 5

-- Test case 3: Simple 2x2 matrix demonstrating diagonal benefit
-- cost = [[1, 10], [10, 1]]
-- Without diagonal: (0,0) → (0,1) → (1,1) = 1+10+1 = 12 or (0,0) → (1,0) → (1,1) = 1+10+1 = 12
-- With diagonal: (0,0) → (1,1) = 1 + 1 = 2
def test3_cost : Array (Array Nat) := #[#[1, 10], #[10, 1]]
def test3_m : Nat := 1
def test3_n : Nat := 1
def test3_Expected : Nat := 2

-- Test case 4: 3x3 matrix where diagonal is clearly beneficial
-- cost = [[1, 5, 5], [5, 1, 5], [5, 5, 1]]
-- Diagonal path: (0,0) → (1,1) → (2,2) = 1 + 1 + 1 = 3
def test4_cost : Array (Array Nat) := #[#[1, 5, 5], #[5, 1, 5], #[5, 5, 1]]
def test4_m : Nat := 2
def test4_n : Nat := 2
def test4_Expected : Nat := 3

-- Test case 5: 4x4 matrix with mixed costs
-- cost = [[1, 3, 5, 8], [4, 2, 1, 7], [4, 3, 2, 3], [1, 2, 3, 2]]
-- One good path: (0,0) → (1,1) → (2,2) → (3,3) = 1 + 2 + 2 + 2 = 7
def test5_cost : Array (Array Nat) := #[#[1, 3, 5, 8], #[4, 2, 1, 7], #[4, 3, 2, 3], #[1, 2, 3, 2]]
def test5_m : Nat := 3
def test5_n : Nat := 3
def test5_Expected : Nat := 7

-- Test case 6: Rectangular matrix (3x4)
-- cost = [[1, 2, 3, 4], [2, 3, 4, 5], [3, 4, 5, 6]]
-- Path: (0,0) → (1,1) → (2,2) → (2,3) = 1 + 3 + 5 + 6 = 15
def test6_cost : Array (Array Nat) := #[#[1, 2, 3, 4], #[2, 3, 4, 5], #[3, 4, 5, 6]]
def test6_m : Nat := 2
def test6_n : Nat := 3
def test6_Expected : Nat := 15

-- Test case 7: All ones (any path has same cost)
-- cost = [[1, 1, 1], [1, 1, 1], [1, 1, 1]]
-- Shortest path with diagonals: (0,0) → (1,1) → (2,2) = 1 + 1 + 1 = 3
def test7_cost : Array (Array Nat) := #[#[1, 1, 1], #[1, 1, 1], #[1, 1, 1]]
def test7_m : Nat := 2
def test7_n : Nat := 2
def test7_Expected : Nat := 3

-- Test case 8: Large values with diagonal advantage
-- cost = [[10, 100, 100], [100, 10, 100], [100, 100, 10]]
-- Diagonal path: (0,0) → (1,1) → (2,2) = 10 + 10 + 10 = 30
def test8_cost : Array (Array Nat) := #[#[10, 100, 100], #[100, 10, 100], #[100, 100, 10]]
def test8_m : Nat := 2
def test8_n : Nat := 2
def test8_Expected : Nat := 30

-- Test case 9: Path to cell in first row (can't use down moves)
-- cost = [[1, 2, 3, 4]]
-- Only path: (0,0) → (0,1) → (0,2) → (0,3) = 1 + 2 + 3 + 4 = 10
def test9_cost : Array (Array Nat) := #[#[1, 2, 3, 4]]
def test9_m : Nat := 0
def test9_n : Nat := 3
def test9_Expected : Nat := 10

-- Test case 10: Path to cell in first column (can't use right moves)
-- cost = [[1], [2], [3], [4]]
-- Only path: (0,0) → (1,0) → (2,0) → (3,0) = 1 + 2 + 3 + 4 = 10
def test10_cost : Array (Array Nat) := #[#[1], #[2], #[3], #[4]]
def test10_m : Nat := 3
def test10_n : Nat := 0
def test10_Expected : Nat := 10

-- Test case 11: Mixed strategy (sometimes diagonal, sometimes not)
-- cost = [[1, 10, 10, 10], [10, 2, 10, 10], [10, 10, 3, 10], [10, 10, 10, 4]]
-- Optimal diagonal path: (0,0) → (1,1) → (2,2) → (3,3) = 1 + 2 + 3 + 4 = 10
def test11_cost : Array (Array Nat) := #[#[1, 10, 10, 10], #[10, 2, 10, 10], #[10, 10, 3, 10], #[10, 10, 10, 4]]
def test11_m : Nat := 3
def test11_n : Nat := 3
def test11_Expected : Nat := 10

-- Test case 12: Where non-diagonal path might be better
-- cost = [[1, 1, 1], [1, 100, 1], [1, 1, 1]]
-- Diagonal: (0,0) → (1,1) → (2,2) = 1 + 100 + 1 = 102
-- Around: (0,0) → (0,1) → (0,2) → (1,2) → (2,2) = 1 + 1 + 1 + 1 + 1 = 5
def test12_cost : Array (Array Nat) := #[#[1, 1, 1], #[1, 100, 1], #[1, 1, 1]]
def test12_m : Nat := 2
def test12_n : Nat := 2
def test12_Expected : Nat := 5

-- Recommend to validate: test cases 1, 2, 3, 4, 7, 12
-- These cover:
-- - Test 1: Problem statement example (required)
-- - Test 2: Single cell edge case
-- - Test 3: Simple case showing clear diagonal benefit
-- - Test 4: Pure diagonal path
-- - Test 7: Uniform cost showing shortest path
-- - Test 12: Case where avoiding diagonal is better

end TestCases
