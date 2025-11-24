import CaseStudies.Velvet.Std
import CaseStudies.TestingUtil

set_option loom.semantics.termination "partial"
set_option loom.semantics.choice "demonic"

section MaxElem

@[grind]
def isMax (mx: Int) (arr: Array Int) :=
    forall i, ( h: i < arr.size ) -> mx >= (arr[i]'h)

method maxElem (arr: Array Int) return (res: Int)
  require arr.size > 0
  ensures isMax res arr
  do
    let mut i := 0
    let mut mx := arr[i]!
    i := i + 1
    while i < arr.size
    invariant 0 <= i ∧ i <= arr.size
    invariant forall j, j < i -> mx >= arr[j]!
    done_with i = arr.size
    do
      let elem := arr[i]!
      if elem > mx then
        mx := elem
      else
        mx := mx
      i := i + 1
    return mx

prove_correct maxElem by
  loom_solve

end MaxElem
