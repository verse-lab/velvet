module

public import Std

namespace VelvetLib.DataStructure

/-!
# Graphs with vertex and edge data

One adjacency-list representation supports all four graph invariants below.
Data types default to `Unit`; edge data can also be any weight type `W` or
`Option W`. Simple graphs have no self-loops or parallel edges, regardless of
edge data. Opposite directed edges are allowed.
-/

/-- An outgoing edge; its source is the vertex storing it. -/
public structure Graph.Edge (EdgeData : Type := Unit) where
  target : Nat
  data : EdgeData
deriving Repr, DecidableEq

public structure Graph.Vertex (VertexData : Type := Unit) (EdgeData : Type := Unit) where
  data : VertexData
  edges : Array (Graph.Edge EdgeData) := #[]
deriving Repr

/-- Vertices are identified by their array indices. Invariants are separate proofs. -/
public structure Graph (VertexData : Type := Unit) (EdgeData : Type := Unit) where
  vertices : Array (Graph.Vertex VertexData EdgeData)
deriving Repr

/-- Outgoing edges; invalid vertex indices yield an empty array. -/
@[expose]
public def Graph.neighbors (graph : Graph VertexData EdgeData) (source : Nat) :
    Array (Graph.Edge EdgeData) :=
  (graph.vertices[source]?.map (·.edges)).getD #[]

/-- Number of outgoing adjacency entries, including loops and parallel edges.
Invalid vertex indices have degree zero. -/
@[expose]
public def Graph.degree (graph : Graph VertexData EdgeData) (vertex : Nat) : Nat :=
  (graph.neighbors vertex).size

/-- Total number of stored adjacency entries; symmetric edges are counted in both directions. -/
@[expose]
public def Graph.edgeCount (graph : Graph VertexData EdgeData) : Nat :=
  (graph.vertices.toList.map fun vertex => vertex.edges.size).sum

/-- Every edge points to an existing vertex. Loops and parallel edges are allowed. -/
public structure DirectedGraphInv (graph : Graph VertexData EdgeData) : Prop where
  targets : ∀ source, ∀ edge ∈ graph.neighbors source, edge.target < graph.vertices.size

/-- Every edge has a reverse edge carrying the same data.
For parallel edges, symmetry concerns existence, not duplicate counts. -/
public structure UndirectedGraphInv (graph : Graph VertexData EdgeData) : Prop
    extends DirectedGraphInv graph where
  symmetric : ∀ source, ∀ edge ∈ graph.neighbors source,
    ⟨source, edge.data⟩ ∈ graph.neighbors edge.target

/-- No self-loops, and at most one outgoing edge to any given target. -/
public structure SimpleDirectedGraphInv (graph : Graph VertexData EdgeData) : Prop
    extends DirectedGraphInv graph where
  loopless : ∀ source, ∀ edge ∈ graph.neighbors source, edge.target ≠ source
  nodup : ∀ source, ((graph.neighbors source).map (·.target)).toList.Nodup

/-- A simple graph with symmetric edges carrying matching data. -/
public structure SimpleUndirectedGraphInv (graph : Graph VertexData EdgeData) : Prop
    extends UndirectedGraphInv graph, SimpleDirectedGraphInv graph where

end VelvetLib.DataStructure
