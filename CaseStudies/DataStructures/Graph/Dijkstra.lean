module

public import CaseStudies.DataStructures.Graph.Distance
public import CaseStudies.DataStructures.PriorityQueue
public meta import CaseStudies.DataStructures.PriorityQueue

open Lean.Grind

namespace VelvetLib.DataStructure.Graph

namespace Dijkstra

/-- Queue entries use reverse lexicographic order, making the max-heap extract
minimum distances. Vertex indices break ties without requiring vertex-data order. -/
public structure Entry (Weight : Type) where
  distance : Weight
  vertex : Nat
deriving Repr

public instance [Zero Weight] : Inhabited (Entry Weight) := ⟨⟨0, 0⟩⟩

public instance [LE Weight] : LE (Entry Weight) where
  le a b := b.distance ≤ a.distance ∧ (a.distance ≤ b.distance → b.vertex ≤ a.vertex)

public instance [LE Weight] [DecidableLE Weight] : DecidableLE (Entry Weight) :=
  fun a b => inferInstanceAs (Decidable
    (b.distance ≤ a.distance ∧ (a.distance ≤ b.distance → b.vertex ≤ a.vertex)))

public instance [LE Weight] [Std.IsLinearOrder Weight] : Std.IsLinearOrder (Entry Weight) where
  le_refl a := by change a.distance ≤ a.distance ∧ _; grind only
  le_trans a b c ab bc := by
    change _ ∧ _ at ab bc ⊢
    grind only
  le_total a b := by
    change (_ ∧ _) ∨ (_ ∧ _)
    grind only
  le_antisymm a b ab ba := by
    cases a; cases b
    change _ ∧ _ at ab ba
    congr <;> grind only

/-- The candidate paths obtained by extending a settled path through each outgoing edge. -/
public def candidates [Add Weight] (graph : Graph VertexData EdgeData)
    (weight : EdgeData → Weight) (entry : Entry Weight) : List (Entry Weight) :=
  (graph.neighbors entry.vertex).toList.map fun edge =>
    ⟨entry.distance + weight edge.data, edge.target⟩

public def work (graph : Graph VertexData EdgeData) (distances : Array (Option Weight))
    (queue : PriorityQueue (Entry Weight)) : Nat :=
  distances.countP Option.isNone * (edgeCount graph + 1) + queue.data.size

/-- Nonnegative edge costs are the additional graph assumption needed by Dijkstra. -/
public def Nonnegative [Zero Weight] [LE Weight] (graph : Graph VertexData EdgeData)
    (weight : EdgeData → Weight) : Prop :=
  ∀ vertex, ∀ edge ∈ graph.neighbors vertex, 0 ≤ weight edge.data

/-- Settled distances are shortest; absent distances denote unreachable vertices. -/
@[expose]
public def Distances [Zero Weight] [Add Weight] [LE Weight]
    (graph : Graph VertexData EdgeData) (weight : EdgeData → Weight) (source : Nat)
    (distances : Array (Option Weight)) : Prop :=
  distances.size = graph.vertices.size ∧
    ∀ vertex, vertex < graph.vertices.size →
      match distances[vertex]! with
      | some distance => graph.IsShortestDistance weight source vertex distance
      | none => ¬graph.Reachable source vertex

/-- Every settled vertex is correct. Each edge leaving the settled region is
represented in the queue, and every queued entry is the cost of an actual path. -/
public structure StateInv [Zero Weight] [Add Weight] [LE Weight]
    (graph : Graph VertexData EdgeData) (weight : EdgeData → Weight) (source : Nat)
    (distances : Array (Option Weight)) (queue : PriorityQueue (Entry Weight)) : Prop where
  size : distances.size = graph.vertices.size
  settled : ∀ vertex distance, distances[vertex]! = some distance →
    graph.IsShortestDistance weight source vertex distance
  paths : ∀ entry ∈ queue.data,
    ∃ path : graph.Path source entry.vertex, path.cost weight = entry.distance
  start : distances[source]!.isSome ∨ ⟨0, source⟩ ∈ queue.data
  frontier : ∀ vertex distance, distances[vertex]! = some distance →
    ∀ edge ∈ graph.neighbors vertex, distances[edge.target]! = none →
      ⟨distance + weight edge.data, edge.target⟩ ∈ queue.data

/-! Algorithm -/

/-- Insert candidates using the priority queue's registered push contract. -/
method enqueue {Weight : Type} [Zero Weight] [LE Weight] [DecidableLE Weight]
    [Std.IsLinearOrder Weight] (queue : PriorityQueue (Entry Weight))
    (items : List (Entry Weight))
  returns (result : PriorityQueue (Entry Weight)) in Id
  requires wellformed: queue.Inv
  ensures wellformed: result.Inv
  ensures elements: result.data.toList.Perm (queue.data.toList ++ items)
do
  let mut result := queue
  let mut remaining := items
  while pending: remaining.isEmpty = false
    invariant heap: result.Inv
    invariant elements: (result.data.toList ++ remaining).Perm (queue.data.toList ++ items)
    decreasing unprocessed: remaining.length
    done_with exhausted: remaining = []
  do
    match remaining with
    | [] => break
    | entry :: tail =>
      result ← PriorityQueue.push result entry
      remaining := tail
  return result

end Dijkstra

open Dijkstra

/-- Dijkstra's single-source shortest paths. `none` denotes unreachable vertices.
The cost type has ordered, associative, commutative addition; stored edge data
is arbitrary. Each vertex is settled once, and stale queue entries are skipped.
The running time is `O(V + (E + 1) log (E + 2))` with constant-time weight operations.
For simple graphs this is `O((V + E) log (V + 1))`. Parallel edges can make
this lazy queue larger; the general `log V` bound needs an indexed queue. -/
method dijkstra {VertexData EdgeData Weight : Type} [AddCommMonoid Weight] [LE Weight] [DecidableLE Weight]
    [Std.IsLinearOrder Weight] [OrderedAdd Weight]
    (graph : Graph VertexData EdgeData) (weight : EdgeData → Weight) (source : Nat)
  returns (distances : Array (Option Weight)) in Id
  requires source_valid: source < graph.vertices.size
  requires wellformed: DirectedGraphInv graph
  requires nonnegative: Dijkstra.Nonnegative graph weight
  ensures shortest: Dijkstra.Distances graph weight source distances
do
  let mut distances : Array (Option Weight) := Array.replicate graph.vertices.size none
  let mut queue : PriorityQueue (Entry Weight) := ⟨#[⟨0, source⟩]⟩
  while pending: 0 < queue.data.size
    invariant heap: queue.Inv
    invariant state: StateInv graph weight source distances queue
    decreasing remaining: work graph distances queue
  do
    let (entry, rest) ← PriorityQueue.pop queue
    queue := rest
    if visited : distances[entry.vertex]!.isSome then
      continue
    distances := distances.set! entry.vertex (some entry.distance)
    queue ← enqueue queue (candidates graph weight entry)
  return distances

namespace Dijkstra

/-! Proof helpers -/

/-- A permutation identifies the removed entry as an entry of the original queue. -/
public theorem removed_mem {before after : Array α} {removed : α}
    (elements : (after.push removed).Perm before) : removed ∈ before :=
  elements.mem_iff.mp Array.mem_push_self

/-- Entries for other vertices remain after removing a queue entry. -/
public theorem retained_mem {before after : Array (Entry Weight)} {removed other : Entry Weight}
    (elements : (after.push removed).Perm before) (member : other ∈ before)
    (different : other.vertex ≠ removed.vertex) : other ∈ after := by
  apply Array.mem_of_ne_of_mem _ (elements.mem_iff.mpr member)
  exact fun equal => different (congrArg Entry.vertex equal)

section Correctness

variable {Weight : Type} [AddCommMonoid Weight] [LE Weight] [Std.IsLinearOrder Weight]
  [OrderedAdd Weight]

public theorem cost_nonnegative {graph : Graph VertexData EdgeData}
    {weight : EdgeData → Weight} (nonnegative : Nonnegative graph weight)
    {source target : Nat} (path : graph.Path source target) : 0 ≤ path.cost weight := by
  induction path with
  | nil => exact Std.IsPreorder.le_refl _
  | cons edge present tail ih =>
    have bound := OrderedAdd.add_le_add (nonnegative _ edge present) ih
    simpa only [AddCommMonoid.zero_add, Path.cost] using bound

omit [LE Weight] [Std.IsLinearOrder Weight] [OrderedAdd Weight] in
public theorem extend_path {graph : Graph VertexData EdgeData}
    (wf : DirectedGraphInv graph) (weight : EdgeData → Weight)
    {source vertex : Nat} {distance : Weight}
    (attained : ∃ path : graph.Path source vertex, path.cost weight = distance)
    (edge : Graph.Edge EdgeData) (present : edge ∈ graph.neighbors vertex) :
    ∃ path : graph.Path source edge.target, path.cost weight = distance + weight edge.data := by
  obtain ⟨path, cost⟩ := attained
  refine ⟨path.append (.cons edge present (.nil (wf.targets vertex edge present))), ?_⟩
  simp only [Path.cost_append, cost, Path.cost, AddCommMonoid.add_zero]

/-- Following a path from the settled region to an unsettled vertex must cross
an edge still represented in the queue. -/
public theorem StateInv.frontier_path {graph : Graph VertexData EdgeData}
    {weight : EdgeData → Weight} {source : Nat} {distances : Array (Option Weight)}
    {queue : PriorityQueue (Entry Weight)} (inv : StateInv graph weight source distances queue)
    (wf : DirectedGraphInv graph) (nonnegative : Nonnegative graph weight)
    {vertex target : Nat} (path : graph.Path vertex target) (distance : Weight)
    (settled : distances[vertex]! = some distance) (unsettled : distances[target]! = none) :
    ∃ entry ∈ queue.data, entry.distance ≤ distance + path.cost weight := by
  induction path generalizing distance with
  | nil => simp_all
  | cons edge present tail ih =>
    cases targetLabel : distances[edge.target]! with
    | none =>
      refine ⟨⟨distance + weight edge.data, edge.target⟩,
        inv.frontier _ distance settled edge present targetLabel, ?_⟩
      have bound := OrderedAdd.add_le_right (distance + weight edge.data)
        (cost_nonnegative nonnegative tail)
      simpa only [AddCommMonoid.add_zero, AddCommMonoid.add_assoc, Path.cost] using bound
    | some next =>
      obtain ⟨entry, member, bound⟩ := ih next targetLabel unsettled
      refine ⟨entry, member, ?_⟩
      obtain ⟨path, cost⟩ :=
        extend_path wf weight (inv.settled _ distance settled).1 edge present
      have edgeBound := (inv.settled edge.target next targetLabel).2 path
      rw [cost] at edgeBound
      have step := OrderedAdd.add_le_left edgeBound (tail.cost weight)
      have result := Std.IsPreorder.le_trans _ _ _ bound step
      simpa only [Path.cost, AddCommMonoid.add_assoc] using result

public theorem StateInv.cover {graph : Graph VertexData EdgeData}
    {weight : EdgeData → Weight} {source : Nat} {distances : Array (Option Weight)}
    {queue : PriorityQueue (Entry Weight)} (inv : StateInv graph weight source distances queue)
    (wf : DirectedGraphInv graph) (nonnegative : Nonnegative graph weight)
    {target : Nat} (path : graph.Path source target) (unsettled : distances[target]! = none) :
    ∃ entry ∈ queue.data, entry.distance ≤ path.cost weight := by
  cases label : distances[source]! with
  | none =>
    exact ⟨⟨0, source⟩, inv.start.resolve_left (by simp [label]),
      cost_nonnegative nonnegative path⟩
  | some distance =>
    obtain ⟨entry, member, bound⟩ := inv.frontier_path wf nonnegative path distance label unsettled
    have zeroBound := (inv.settled source distance label).2 (.nil path.source_valid)
    have upper := OrderedAdd.add_le_left zeroBound (path.cost weight)
    exact ⟨entry, member, Std.IsPreorder.le_trans _ _ _ bound
      (by simpa [Path.cost, AddCommMonoid.zero_add] using upper)⟩

public theorem StateInv.minimum_shortest {graph : Graph VertexData EdgeData}
    {weight : EdgeData → Weight} {source : Nat} {distances : Array (Option Weight)}
    {queue rest : PriorityQueue (Entry Weight)} {entry : Entry Weight}
    (inv : StateInv graph weight source distances queue)
    (wf : DirectedGraphInv graph) (nonnegative : Nonnegative graph weight)
    (elements : (rest.data.push entry).Perm queue.data)
    (maximum : ∀ i, i < queue.data.size → queue.data[i]! ≤ entry)
    (unsettled : distances[entry.vertex]! = none) :
    graph.IsShortestDistance weight source entry.vertex entry.distance := by
  refine ⟨inv.paths entry (removed_mem elements), ?_⟩
  intro path
  obtain ⟨other, member, bound⟩ := inv.cover wf nonnegative path unsettled
  obtain ⟨i, bounded, eq⟩ := Array.mem_iff_getElem.mp member
  have ordered := maximum i bounded
  rw [getElem!_pos queue.data i bounded, eq] at ordered
  exact Std.IsPreorder.le_trans _ _ _ ordered.1 bound

public theorem StateInv.finished {graph : Graph VertexData EdgeData}
    {weight : EdgeData → Weight} {source : Nat} {distances : Array (Option Weight)}
    {queue : PriorityQueue (Entry Weight)} (inv : StateInv graph weight source distances queue)
    (wf : DirectedGraphInv graph) (nonnegative : Nonnegative graph weight)
    (empty : queue.data.size = 0) : Distances graph weight source distances := by
  refine ⟨inv.size, ?_⟩
  intro vertex valid
  cases label : distances[vertex]! with
  | some distance => exact inv.settled vertex distance label
  | none =>
    intro reachable
    obtain ⟨path⟩ := reachable
    obtain ⟨entry, member, _⟩ := inv.cover wf nonnegative path label
    have nil : queue.data = #[] := Array.size_eq_zero_iff.mp empty
    simp [nil] at member

omit [Std.IsLinearOrder Weight] [OrderedAdd Weight] in
public theorem StateInv.skip {graph : Graph VertexData EdgeData}
    {weight : EdgeData → Weight} {source : Nat} {distances : Array (Option Weight)}
    {queue rest : PriorityQueue (Entry Weight)} {entry : Entry Weight}
    (inv : StateInv graph weight source distances queue)
    (elements : (rest.data.push entry).Perm queue.data)
    (visited : distances[entry.vertex]!.isSome) : StateInv graph weight source distances rest := by
  refine ⟨inv.size, inv.settled, ?_, ?_, ?_⟩
  · intro other member
    exact inv.paths other
      (elements.mem_iff.mp (Array.mem_push_of_mem entry member))
  · rcases inv.start with settled | queued
    · exact Or.inl settled
    · by_cases same : source = entry.vertex
      · exact Or.inl (by simpa [same] using visited)
      · exact Or.inr (retained_mem elements queued same)
  · intro vertex distance settled edge present unset
    apply retained_mem elements (inv.frontier vertex distance settled edge present unset)
    intro same
    change edge.target = entry.vertex at same
    rw [← same, unset] at visited
    contradiction

public theorem StateInv.settle {graph : Graph VertexData EdgeData}
    {weight : EdgeData → Weight} {source : Nat} {distances : Array (Option Weight)}
    {queue rest next : PriorityQueue (Entry Weight)} {entry : Entry Weight}
    (inv : StateInv graph weight source distances queue)
    (wf : DirectedGraphInv graph) (nonnegative : Nonnegative graph weight)
    (elements : (rest.data.push entry).Perm queue.data)
    (maximum : ∀ i, i < queue.data.size → queue.data[i]! ≤ entry)
    (unsettled : distances[entry.vertex]! = none)
    (inserted : next.data.toList.Perm (rest.data.toList ++ candidates graph weight entry)) :
    StateInv graph weight source (distances.set! entry.vertex (some entry.distance))
      next := by
  have valid := (inv.paths entry (removed_mem elements)).choose.target_valid
  have bounded : entry.vertex < distances.size := by rw [inv.size]; exact valid
  have shortest := inv.minimum_shortest wf nonnegative elements maximum unsettled
  have members : ∀ other, other ∈ next.data ↔
      other ∈ rest.data ∨ other ∈ candidates graph weight entry := by
    intro other
    simpa using inserted.mem_iff (a := other)
  have updated :
      (distances.set! entry.vertex (some entry.distance))[entry.vertex]! =
        some entry.distance :=
    Array.getElem!_set!_self _ _ _ bounded
  have unchanged {vertex : Nat} (different : vertex ≠ entry.vertex) :
      (distances.set! entry.vertex (some entry.distance))[vertex]! = distances[vertex]! :=
    Array.getElem!_set!_ne _ _ _ _ (Ne.symm different)
  refine ⟨by simpa using inv.size, ?_, ?_, ?_, ?_⟩
  · intro vertex distance label
    by_cases same : vertex = entry.vertex
    · subst vertex
      rw [updated] at label
      cases label
      exact shortest
    · rw [unchanged same] at label
      exact inv.settled vertex distance label
  · intro other member
    rcases (members other).mp member with remaining | candidate
    · exact inv.paths other
        (elements.mem_iff.mp (Array.mem_push_of_mem entry remaining))
    · simp only [candidates, List.mem_map, Array.mem_toList_iff] at candidate
      obtain ⟨edge, present, rfl⟩ := candidate
      exact extend_path wf weight shortest.1 edge present
  · by_cases same : source = entry.vertex
    · left
      rw [same, updated]
      rfl
    · rw [unchanged same]
      exact inv.start.imp id fun member =>
        (members _).mpr (Or.inl (retained_mem elements member same))
  · intro vertex distance label edge present unset
    have targetNe : edge.target ≠ entry.vertex := by
      intro same
      rw [same, updated] at unset
      contradiction
    rw [unchanged targetNe] at unset
    by_cases same : vertex = entry.vertex
    · subst vertex
      rw [updated] at label
      cases label
      apply (members _).mpr
      right
      simp only [candidates, List.mem_map, Array.mem_toList_iff]
      exact ⟨edge, present, rfl⟩
    · rw [unchanged same] at label
      exact (members _).mpr (Or.inl
        (retained_mem elements (inv.frontier vertex distance label edge present unset) targetNe))

end Correctness

public theorem replicate_none (count vertex : Nat) :
    (Array.replicate count (none : Option Weight))[vertex]! = none := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

public theorem initial [Zero Weight] [Add Weight] [LE Weight]
    (graph : Graph VertexData EdgeData) (weight : EdgeData → Weight) (source : Nat)
    (valid : source < graph.vertices.size) :
    StateInv graph weight source (Array.replicate graph.vertices.size none)
      ⟨#[⟨0, source⟩]⟩ := by
  refine ⟨by simp, ?_, ?_, Or.inr (by simp), ?_⟩
  · simp [replicate_none]
  · intro entry member
    simp only [Array.mem_singleton] at member
    subst entry
    exact ⟨.nil valid, rfl⟩
  · simp [replicate_none]

public theorem skip_decreases
    {graph : Graph VertexData EdgeData} {distances : Array (Option Weight)}
    {queue rest : PriorityQueue (Entry Weight)} {entry : Entry Weight}
    (elements : (rest.data.push entry).Perm queue.data) :
    work graph distances rest < work graph distances queue := by
  have size := elements.size_eq
  simp only [Array.size_push] at size
  unfold work
  omega

public theorem settle_decreases [Zero Weight] [Add Weight] [LE Weight]
    {graph : Graph VertexData EdgeData}
    {weight : EdgeData → Weight} {source : Nat} {distances : Array (Option Weight)}
    {queue rest next : PriorityQueue (Entry Weight)} {entry : Entry Weight}
    (inv : StateInv graph weight source distances queue)
    (elements : (rest.data.push entry).Perm queue.data)
    (unset : distances[entry.vertex]! = none)
    (inserted : next.data.toList.Perm (rest.data.toList ++ candidates graph weight entry)) :
    work graph (distances.set! entry.vertex (some entry.distance)) next <
      work graph distances queue := by
  have valid := (inv.paths entry (removed_mem elements)).choose.target_valid
  have bounded : entry.vertex < distances.size := by rw [inv.size]; exact valid
  have indexed : distances[entry.vertex] = none := by
    rwa [getElem!_pos distances entry.vertex bounded] at unset
  have counts : (distances.set! entry.vertex (some entry.distance)).countP Option.isNone + 1 =
      distances.countP Option.isNone := by
    have positive := Array.boole_getElem_le_countP (p := Option.isNone) bounded
    simp only [indexed, Option.isNone_none, ↓reduceIte] at positive
    rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds]
    simp only [bounded, ↓reduceDIte, Array.countP_set, indexed,
      Option.isNone_none, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    omega
  have sizes : next.data.size = rest.data.size + (graph.neighbors entry.vertex).size := by
    simpa [candidates] using inserted.length_eq
  have degree : (graph.neighbors entry.vertex).size ≤ graph.edgeCount := by
    have member : graph.vertices[entry.vertex].edges.toList ∈
        graph.vertices.toList.map (fun vertex => vertex.edges.toList) :=
      List.mem_map.mpr ⟨_, Array.getElem_mem_toList valid, rfl⟩
    have bound := (List.sublist_flatten_of_mem member).length_le
    simpa [Graph.degree, Graph.neighbors, getElem?_pos graph.vertices entry.vertex valid,
      Graph.edgeCount, List.length_flatten, List.map_map, Function.comp_def] using bound
  have removed := elements.size_eq
  simp only [Array.size_push] at removed
  unfold work
  rw [← counts, Nat.add_mul]
  simp only [Nat.one_mul]
  omega

/-! Correctness proofs -/

prove_correct enqueue by
  velvet_vcgen [enqueue] <;> try assumption
  · exact .refl _
  · simpa [exhausted] using elements
  · simp [h_cons]
  · apply (elements_1.toList.append_right tail).trans
    simpa [Array.toList_push, List.append_assoc, h_cons] using elements
  · cases remaining <;> simp_all

end Dijkstra

prove_correct dijkstra by
  velvet_vcgen [dijkstra] <;> try assumption
  · refine ⟨?_⟩
    intro child positive bounded _
    simp at bounded
    omega
  · exact initial _ _ _ source_valid
  · exact state.finished wellformed nonnegative (by omega)
  · exact skip_decreases elements
  · exact state.skip elements visited
  · exact settle_decreases state elements (by simpa using visited) elements_1
  · exact state.settle wellformed nonnegative elements maximum
      (by simpa using visited) elements_1

end VelvetLib.DataStructure.Graph
