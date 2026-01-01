import CaseStudies.Velvet.SpecDSL

-- Comprehensive test of specdef functionality

-- Test 1: Basic pre/post conditions with simple function
specdef BasicTest

def_pre (n : Nat) : n > 0
def_post (n : Nat) (result : Nat) : result >= n

def increment (n : Nat) : Nat := n + 1

specend BasicTest

-- Verify accessibility
#check BasicTest.pre         -- Should work!
#check BasicTest.post        -- Should work!
#check BasicTest.increment   -- Should work!

-- Test 2: Multiple parameters
specdef MultiParam

def_pre (x : Nat) (y : Nat) : x > 0 ∧ y > 0
def_post (x : Nat) (y : Nat) (result : Nat) : result = x + y

def add (x y : Nat) : Nat := x + y

specend MultiParam

#check MultiParam.pre   -- (x y : Nat) : Prop
#check MultiParam.post  -- (x y : Nat) (result : Nat) : Prop
#check MultiParam.add

-- Test 3: Complex postcondition
specdef ComplexPost

def_pre (n : Nat) : n < 100
def_post (n : Nat) (result : Nat) : result > n ∧ result < n + 10

def addSmall (n : Nat) : Nat := n + 5

specend ComplexPost

#check ComplexPost.pre
#check ComplexPost.post
#check ComplexPost.addSmall
