module

public import CaseStudies.DataStructures.Graph.Reachability
public import Init.Grind.Module.Basic

namespace VelvetLib.DataStructure.Graph

/-- Total cost of a path. Use `id` for stored weights and `fun _ => 1` for
unweighted edges. Optional edge weights require an explicit cost policy. -/
@[expose]
public def Path.cost {Weight : Type} [Zero Weight] [Add Weight]
    {graph : Graph VertexData EdgeData} {source target : Nat}
    (weight : EdgeData → Weight) (path : graph.Path source target) : Weight :=
  match path with
  | .nil _ => 0
  | .cons edge _ tail => weight edge.data + tail.cost weight

public theorem Path.cost_append {Weight : Type} [Lean.Grind.AddCommMonoid Weight]
    {graph : Graph VertexData EdgeData} (weight : EdgeData → Weight)
    {source middle target : Nat} (first : graph.Path source middle)
    (second : graph.Path middle target) :
    (first.append second).cost weight = first.cost weight + second.cost weight := by
  induction first with
  | nil => simp [Path.append, Path.cost, Lean.Grind.AddCommMonoid.zero_add]
  | cons edge present tail ih =>
    simp [Path.append, Path.cost, ih, Lean.Grind.AddCommMonoid.add_assoc]

/-- `distance` is attained by a path and is no greater than any other path cost. -/
@[expose]
public def IsShortestDistance {Weight : Type} [Zero Weight] [Add Weight] [LE Weight]
    (graph : Graph VertexData EdgeData) (weight : EdgeData → Weight)
    (source target : Nat) (distance : Weight) : Prop :=
  (∃ path : graph.Path source target, path.cost weight = distance) ∧
    ∀ path : graph.Path source target, distance ≤ path.cost weight

end VelvetLib.DataStructure.Graph
