module

public import CaseStudies.DataStructures.Graph.Graph

namespace VelvetLib.DataStructure.Graph

/-- A finite directed path. Edges retain their data, distinguishing parallel edges.
The empty path exists only at a valid vertex. -/
public inductive Path (graph : Graph VertexData EdgeData) : Nat → Nat → Type where
  | nil {vertex : Nat} (valid : vertex < graph.vertices.size) : Path graph vertex vertex
  | cons {source target : Nat} (edge : Graph.Edge EdgeData)
      (present : edge ∈ graph.neighbors source) (tail : Path graph edge.target target) :
      Path graph source target

public theorem Path.source_valid {graph : Graph VertexData EdgeData} {source target : Nat}
    (path : graph.Path source target) : source < graph.vertices.size := by
  cases path with
  | nil valid => exact valid
  | cons edge present tail =>
    by_cases valid : source < graph.vertices.size
    · exact valid
    · simp [neighbors, getElem?_neg graph.vertices source valid] at present

public theorem Path.target_valid {graph : Graph VertexData EdgeData} {source target : Nat}
    (path : graph.Path source target) : target < graph.vertices.size := by
  induction path with
  | nil valid => exact valid
  | cons _ _ _ ih => exact ih

/-- There is a finite path from `source` to `target`. -/
@[expose]
public def Reachable (graph : Graph VertexData EdgeData) (source target : Nat) : Prop :=
  Nonempty (graph.Path source target)

/-- Concatenate paths whose endpoints agree. -/
@[expose]
public def Path.append {graph : Graph VertexData EdgeData} {source middle target : Nat}
    (first : graph.Path source middle) (second : graph.Path middle target) :
    graph.Path source target :=
  match first with
  | .nil _ => second
  | .cons edge present tail => .cons edge present (tail.append second)

public theorem Reachable.refl {graph : Graph VertexData EdgeData} {vertex : Nat}
    (valid : vertex < graph.vertices.size) : graph.Reachable vertex vertex :=
  ⟨.nil valid⟩

public theorem Reachable.trans {graph : Graph VertexData EdgeData} {source middle target : Nat}
    (first : graph.Reachable source middle) (second : graph.Reachable middle target) :
    graph.Reachable source target := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  exact ⟨first.append second⟩

public theorem reachable_of_edge {graph : Graph VertexData EdgeData}
    (wf : DirectedGraphInv graph) {source : Nat} {edge : Graph.Edge EdgeData}
    (present : edge ∈ graph.neighbors source) : graph.Reachable source edge.target :=
  ⟨.cons edge present (.nil (wf.targets source edge present))⟩

end VelvetLib.DataStructure.Graph
