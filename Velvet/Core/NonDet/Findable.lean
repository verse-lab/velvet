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

/-- Construct a complete `Findable` instance from a finder and its two correctness proofs. -/
@[instance_reducible]
public def Findable.ofFn {α : Type u} {p : α → Prop}
    (find : Unit → Option α)
    (hnone : (find ()).isNone → ∀ x, ¬ p x)
    (hsome : ∀ x, find () = some x → p x) : Findable p :=
  ⟨find, hnone, fun h => hsome _ h⟩

/-- Accessibility witness for an unbounded natural-number search. -/
public inductive AccFrom (p : Nat → Prop) : Nat → Prop where
  | now : p i → AccFrom p i
  | later : ¬ p i → AccFrom p (i + 1) → AccFrom p i

/-- Unbounded semidecision search starting at `i`. If no witness exists, it diverges. -/
public def findNatAux (p : Nat → Prop) [DecidablePred p] (i : Nat) : Option Nat :=
  if p i then some i else findNatAux p (i + 1)
  partial_fixpoint

/-- Search for the least natural number satisfying `p`; diverges when no witness exists. -/
public def findNat (p : Nat → Prop) [DecidablePred p] : Option Nat :=
  findNatAux p 0

public theorem AccFrom.findNatAux_isSome (p : Nat → Prop) [DecidablePred p] (i : Nat) :
    AccFrom p i → (findNatAux p i).isSome := by
  intro h
  induction h with
  | now hp => unfold findNatAux; simp [hp]
  | later hpi _ ih => unfold findNatAux; simp [hpi, ih]

public theorem AccFrom.of_le (p : Nat → Prop) [DecidablePred p] {i x : Nat}
    (hix : i ≤ x) (hp : p x) : AccFrom p i := by
  by_cases hi : p i
  · exact .now hi
  · by_cases heq : i = x
    · subst x; contradiction
    · exact .later hi (AccFrom.of_le p (i := i + 1) (x := x) (by omega) hp)
termination_by x - i
decreasing_by omega

public theorem findNat_some {p : Nat → Prop} [DecidablePred p] {res : Nat}
    (h : findNat p = some res) : p res := by
  apply findNatAux.partial_correctness (motive := fun _ r => p r) p
  · intro aux ih i r hr
    split at hr
    · rename_i hp; cases hr; exact hp
    · exact ih _ _ hr
  · exact h

public theorem exists_findNat (p : Nat → Prop) [DecidablePred p] :
    (∃ x, p x) ↔ (findNat p).isSome := by
  constructor
  · rintro ⟨x, px⟩
    exact AccFrom.findNatAux_isSome p 0 (AccFrom.of_le p (Nat.zero_le x) px)
  · simp only [Option.isSome_iff_exists]
    rintro ⟨x, hx⟩
    exact ⟨x, findNat_some hx⟩

public theorem findNat_none (p : Nat → Prop) [DecidablePred p] :
    (findNat p).isNone → ∀ x, ¬ p x := by
  intro hn x hp
  have hs : (findNat p).isSome := (exists_findNat p).mp ⟨x, hp⟩
  simp only [Option.isNone_iff_eq_none] at hn
  simp [hn] at hs

public instance (priority := 50) findNatFindable (p : Nat → Prop) [DecidablePred p] :
    Findable p where
  find _ := findNat p
  find_none := findNat_none p
  find_some_p := findNat_some

/-- Candidate generator for integer search, alternating non-negative and negative:
`0, -1, 1, -2, 2, -3, 3, ...` -/
public def intCand (i : Nat) : Int :=
  if i % 2 = 0 then (i / 2 : Nat) else -((i + 1) / 2 : Nat)

/-- Position of an integer in `intCand`'s enumeration. -/
public def intIndex : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

public theorem intCand_intIndex (z : Int) : intCand (intIndex z) = z := by
  cases z with
  | ofNat n => simp [intCand, intIndex]
  | negSucc n => simp [intCand, intIndex]; omega

/-- Complete integer search obtained from the unbounded natural-number search. -/
public def findInt (p : Int → Prop) [DecidablePred p] : Option Int :=
  (findNat (fun n => p (intCand n))).map intCand

public theorem findInt_none (p : Int → Prop) [DecidablePred p] :
    (findInt p).isNone → ∀ z, ¬ p z := by
  intro hn z hp
  have hs : (findNat (fun n => p (intCand n))).isSome :=
    (exists_findNat _).mp ⟨intIndex z, by simpa [intCand_intIndex] using hp⟩
  simp only [findInt, Option.isNone_map] at hn
  simp only [Option.isNone_iff_eq_none] at hn
  simp [hn] at hs

public theorem findInt_some {p : Int → Prop} [DecidablePred p] {res : Int}
    (h : findInt p = some res) : p res := by
  unfold findInt at h
  cases hs : findNat (fun n => p (intCand n)) with
  | none => simp [hs] at h
  | some n =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      subst res
      exact findNat_some hs

public instance (priority := 50) findIntFindable (p : Int → Prop) [DecidablePred p] :
    Findable p where
  find _ := findInt p
  find_none := findInt_none p
  find_some_p := findInt_some

end

