namespace Internal

def Set (α : Type u) : Type u := α → Prop

def Set.mem (x : α) (s : Set α) : Prop := s x

def Set.mkSingleton (x : α) : Set α := fun y => y = x

inductive Set.IsSingleton (s : Set α) : Prop where
  | intro (x : α) : (∀ y, s.mem y ↔ y = x) → s.IsSingleton

theorem Set.mk_singleton_is_singleton (x : α) : (Set.mkSingleton x).IsSingleton := by
  apply Set.IsSingleton.intro x
  simp [mkSingleton, mem]

end Internal

section Ghost
open Internal


structure Ghost (α : Type u) : Type u where
  protected mk' ::
  protected toSet : Set α
  protected isSingleton : toSet.IsSingleton



theorem Ghost.exists_unique (s : Ghost α) : ∃ x, ∀ y, s.toSet.mem y ↔ y = x := by
  rcases s.isSingleton with ⟨x, hx⟩
  exact ⟨x, hx⟩

public def Ghost.mk (x : α) : Ghost α := ⟨Set.mkSingleton x, Set.mk_singleton_is_singleton x⟩

instance Ghost.instNonempty [Nonempty α] : Nonempty (Ghost α) :=
  ⟨Ghost.mk Classical.ofNonempty⟩

public noncomputable def Ghost.reveal (s : Ghost α) : α := s.exists_unique.choose

public def Ghost.modify (s : Ghost α) (f : α → α) : Ghost α :=
  ⟨fun x => ∃ y, s.toSet.mem y ∧ f y = x,
  by
    rcases s.isSingleton with ⟨x, hx⟩
    apply Set.IsSingleton.intro (f x)
    intro y
    constructor
    · rintro ⟨z, hz, hfz⟩
      calc
        y = f z := hfz.symm
        _ = f x := congrArg f ((hx z).mp hz)
    · intro hy
      exact ⟨x, (hx x).mpr rfl, hy.symm⟩ ⟩

public def Ghost.bind {α : Type u} {β : Type u'} (s : Ghost α) (k : α → Ghost β) : Ghost β :=
  ⟨fun z => ∃ x, s.toSet.mem x ∧ (k x).toSet.mem z,
  by
    rcases s.isSingleton with ⟨x₀, hx₀⟩
    rcases (k x₀).isSingleton with ⟨z₀, hz₀⟩
    apply Set.IsSingleton.intro z₀
    intro y
    constructor
    · rintro ⟨x, hx, hy⟩
      have hxx₀ : x = x₀ := (hx₀ x).mp hx
      subst hxx₀
      exact (hz₀ y).mp hy
    · intro hy
      have hx : s.toSet.mem x₀ := (hx₀ x₀).mpr rfl
      have hy' : (k x₀).toSet.mem y := (hz₀ y).mpr hy
      exact ⟨x₀, hx, hy'⟩⟩

instance : Monad Ghost where
  pure := Ghost.mk
  bind s k := Ghost.bind s k

@[grind =, simp]
public theorem Ghost.reveal_bind {α : Type u} {β : Type u} (s : Ghost α) (k : α → Ghost β) :
    (Ghost.bind s k).reveal = (k s.reveal).reveal := by
  have hs := Classical.choose_spec s.exists_unique
  have hsget : s.toSet.mem s.reveal := (hs s.reveal).mpr rfl
  have hk := Classical.choose_spec (k s.reveal).exists_unique
  have hkget : (k s.reveal).toSet.mem (k s.reveal).reveal := (hk (k s.reveal).reveal).mpr rfl
  have hbind :
      ∀ y, (Ghost.bind s k).toSet.mem y ↔ y = (Ghost.bind s k).reveal :=
    Classical.choose_spec (Ghost.bind s k).exists_unique
  exact ((hbind (k s.reveal).reveal).mp ⟨s.reveal, hsget, hkget⟩).symm

/- `Ghost.reveal_bind` is stated for the concrete `Ghost.bind`; the `do`/`>>=` sugar elaborates to
`Bind.bind (Monad.toBind instMonadGhost)`, which is only *definitionally* `Ghost.bind`. `simp`/`grind`
do not unfold the `Monad Ghost` instance, so we register a version in `>>=` form as well. -/
@[grind =, simp]
public theorem Ghost.reveal_do {α : Type u} {β : Type u} (s : Ghost α) (k : α → Ghost β) :
    (s >>= k).reveal = (k s.reveal).reveal := by
  exact Ghost.reveal_bind s k


@[grind =, simp]
public theorem Ghost.reveal_mk {α : Type u} (x : α) :
    (Ghost.mk x).reveal = x := by
  have h :
      ∀ y, (Ghost.mk x).toSet.mem y ↔ y = (Ghost.mk x).reveal :=
    Classical.choose_spec (Ghost.mk x).exists_unique
  exact ((h x).mp (by simp [Ghost.mk, Set.mkSingleton, Set.mem])).symm

@[grind =, simp]
public theorem Ghost.mk_reveal {α : Type u} (s : Ghost α) :
    Ghost.mk s.reveal = s := by
  cases s with                                                                          
  | mk' toSet isSingleton =>                                                            
    unfold Ghost.mk                                                              
    congr                                                                               
    funext y                                                                            
    apply propext                                                                       
    have h :
        ∀ y,
          (Ghost.mk' toSet isSingleton).toSet.mem y ↔
            y = (Ghost.mk' toSet isSingleton).reveal :=
      Classical.choose_spec (Ghost.mk' toSet isSingleton).exists_unique
    constructor                                                                         
    · intro hy                                                                          
      exact (h y).mpr hy                                                                
    · intro hy                                                                          
      exact (h y).mp hy                                                                 

@[grind =, simp]
public theorem Ghost.reveal_modify {α : Type u} (s : Ghost α) (f : α → α) :
    (Ghost.modify s f).reveal = f (s.reveal) := by
  have hs := Classical.choose_spec s.exists_unique               
  have hmod :
      ∀ y, (Ghost.modify s f).toSet.mem y ↔
        y = (Ghost.modify s f).reveal :=
    Classical.choose_spec (Ghost.modify s f).exists_unique
  have hsget : s.toSet.mem s.reveal := (hs s.reveal).mpr rfl           
  exact ((hmod (f s.reveal)).mp ⟨s.reveal, hsget, rfl⟩).symm           

@[ext, grind .]
public theorem Ghost.ext {α : Type u} {a b : Ghost α}
    (h : a.reveal = b.reveal) : a = b := by
  rw [← Ghost.mk_reveal a, ← Ghost.mk_reveal b, h]

end Ghost 
