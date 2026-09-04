module

universe u v

@[expose] public section

/-- WeakFindable: witnessing that `find () = some x` implies `p x`. -/
public class WeakFindable {α : Type u} (p : α → Prop) where
  find : Unit → Option α
  find_some_p : find () = some x → p x

/-- Findable: computable choice operator for property `p`.
If a witness is found, `p x` holds. If `none` is returned, then no such witness exists. -/
public class Findable {α : Type u} (p : α → Prop) where
  find : Unit → Option α
  find_none : (find ()).isNone → ∀ x, ¬ p x
  find_some_p : find () = some x → p x

public instance (priority := high) WeakFindable.of_Findable {α : Type u} (p : α → Prop) [Findable p] :
    WeakFindable p where
  find := Findable.find p
  find_some_p := Findable.find_some_p

/-- Any inhabited type has a trivial findable search for `fun _ => True`. -/
public instance (priority := default) Findable.of_inhabited {α : Type u} [Inhabited α] :
    Findable (fun (_ : α) => True) where
  find := fun _ => some default
  find_none := by intro h; contradiction
  find_some_p := by intros; trivial

/-- Decidable proposition over `PUnit` is findable. -/
public instance Findable.of_decidable_punit (as : Prop) [Decidable as] :
    Findable (α := PUnit.{u+1}) (fun _ => as) where
  find := fun _ => if as then some .unit else none
  find_none := by
    intro h x ha
    by_cases has : as
    · simp [has] at h
    · contradiction
  find_some_p := by
    intro x h
    by_cases has : as
    · exact has
    · simp [has] at h

/-- Simple enumerable typeclass for finite types, allowing search over a list of candidates. -/
public class Finitary (α : Type u) where
  elems : List α
  complete : ∀ x : α, x ∈ elems

public instance : Finitary Bool where
  elems := [false, true]
  complete := by intro x; cases x <;> simp

public instance : Finitary PUnit.{u+1} where
  elems := [.unit]
  complete := by intro x; cases x; simp

public instance (n : Nat) : Finitary (Fin n) where
  elems := List.finRange n
  complete := by intro x; exact List.mem_finRange x


public instance [Finitary α] [Finitary β] : Finitary (α × β) where
  elems := Finitary.elems.flatMap (fun a => Finitary.elems.map (fun b => (a, b)))
  complete := by
    intro ⟨a, b⟩
    have ha := Finitary.complete a
    have hb := Finitary.complete b
    simp [ha, hb]

/-- Finite decidable predicates are findable by linear search. -/
public instance (priority := low) Findable.of_finitary {α : Type u} (p : α → Prop)
    [Finitary α] [DecidablePred p] : Findable p where
  find := fun _ => Finitary.elems.find? (fun a => p a)
  find_none := by
    intro h x hp
    have hx := Finitary.complete x
    have hnone : Finitary.elems.find? (fun a => p a) = none := Option.isNone_iff_eq_none.mp h
    have hfind := List.find?_eq_none.mp hnone
    have hp_dec : (fun a => decide (p a)) x = true := by simp [hp]
    exact (hfind x hx) hp_dec
  find_some_p := by
    intro x h
    have hsome := List.find?_some h
    simp at hsome
    exact hsome

/-- FindHint provides an optional heuristic search for non-deterministic choice extraction.
If a `WeakFindable` or `Findable` instance is available, it is used; otherwise it falls back to `none`. -/
public class FindHint {α : Type u} (p : α → Prop) where
  find : Unit → Option α

public instance (priority := 10) defaultFindHint {α : Type u} (p : α → Prop) : FindHint p where
  find _ := none

public instance (priority := 100) findHintOfWeakFindable {α : Type u} (p : α → Prop) [wf : WeakFindable p] : FindHint p where
  find := wf.find

/-- Search for a natural number satisfying a decidable predicate up to `maxSteps` (default 10000). -/
public def findNat (p : Nat → Prop) [DecidablePred p] (maxSteps : Nat := 10000) : Option Nat :=
  let rec aux (i : Nat) : Option Nat :=
    if i ≥ maxSteps then none
    else if p i then some i
    else aux (i + 1)
  aux 0

public instance (priority := 50) findHintNat (p : Nat → Prop) [DecidablePred p] : FindHint p where
  find _ := findNat p

end

