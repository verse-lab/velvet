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


structure Ghost (α : Type u) : Type (max u v) where
  protected mk' ::
  protected toSet : Set α
  protected isSingleton : toSet.IsSingleton



theorem Ghost.exists_unique (s : Ghost α) : ∃ x, ∀ y, s.toSet.mem y ↔ y = x := by
  rcases s.isSingleton with ⟨x, hx⟩
  exact ⟨x, hx⟩

def Ghost.mk (x : α) : Ghost α := ⟨Set.mkSingleton x, Set.mk_singleton_is_singleton x⟩

instance Ghost.instNonempty [Nonempty α] : Nonempty (Ghost α) :=
  ⟨Ghost.mk Classical.ofNonempty⟩

noncomputable
def Ghost.reveal (s : Ghost α) : α := s.exists_unique.choose

def Ghost.modify (s : Ghost α) (f : α → α) : Ghost α :=
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


@[grind =, simp]
theorem Ghost.reveal_mk.{u, v} {α : Type u} (x : α) :
    (Ghost.mk.{u, v} x).reveal = x := by
  have h :
      ∀ y, (Ghost.mk.{u, v} x).toSet.mem y ↔ y = (Ghost.mk.{u, v} x).reveal :=
    Classical.choose_spec (Ghost.mk.{u, v} x).exists_unique
  exact ((h x).mp (by simp [Ghost.mk, Set.mkSingleton, Set.mem])).symm

@[grind =, simp]
theorem Ghost.mk_reveal.{u, v} {α : Type u} (s : Ghost.{u, v} α) :
    Ghost.mk.{u, v} s.reveal = s := by
  cases s with                                                                          
  | mk' toSet isSingleton =>                                                            
    unfold Ghost.mk                                                              
    congr                                                                               
    funext y                                                                            
    apply propext                                                                       
    have h :
        ∀ y,
          (Ghost.mk'.{u, v} toSet isSingleton).toSet.mem y ↔
            y = (Ghost.mk'.{u, v} toSet isSingleton).reveal :=
      Classical.choose_spec (Ghost.mk'.{u, v} toSet isSingleton).exists_unique
    constructor                                                                         
    · intro hy                                                                          
      exact (h y).mpr hy                                                                
    · intro hy                                                                          
      exact (h y).mp hy                                                                 

@[grind =, simp]
theorem Ghost.reveal_modify.{u, v} {α : Type u} (s : Ghost.{u, v} α) (f : α → α) :
    (Ghost.modify.{u, v, v} s f).reveal = f (s.reveal) := by
  have hs := Classical.choose_spec s.exists_unique               
  have hmod :
      ∀ y, (Ghost.modify.{u, v, v} s f).toSet.mem y ↔
        y = (Ghost.modify.{u, v, v} s f).reveal :=
    Classical.choose_spec (Ghost.modify.{u, v, v} s f).exists_unique
  have hsget : s.toSet.mem s.reveal := (hs s.reveal).mpr rfl           
  exact ((hmod (f s.reveal)).mp ⟨s.reveal, hsget, rfl⟩).symm           

@[ext, grind .]
theorem Ghost.ext.{u, v} {α : Type u} {a b : Ghost.{u, v} α}
    (h : a.reveal = b.reveal) : a = b := by
  rw [← Ghost.mk_reveal a, ← Ghost.mk_reveal b, h]

end Ghost 
