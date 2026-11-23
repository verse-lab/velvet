import Colean

/-!
# Interaction trees

The coinductive type of interaction trees, defined with the `codatatype` command of `colean`
(https://github.com/verse-lab/colean), with its monad structure, events and traces. Loops are
Velvet's `while`, whose `partial_fixpoint` needs the `CCPO` and `MonoBind` instances here. The weakest precondition is in `Velvet/Examples/ITree/WP.lean`.

`@[with_ccpo]` orders trees by approximation, with `div` at the bottom, so programs (`bind`,
loops) are defined by Lean's `partial_fixpoint`.
-/

open Lean.Order

/-! ## 1. Interaction trees

After `ColeanTest/ITree.lean` and `ColeanTest/CCPO.lean` of colean (Apache-2.0). -/

@[with_ccpo]
codatatype ITree (E : Type → Type) (R : Type)
  | ret (r : R)
  | vis {X : Type} (e : E X) (k : X → ITree E R)
  | div

noncomputable section

variable {E : Type → Type} {R S : Type}

/-- Trigger an event and return its answer. -/
def ITree.trigger {X : Type} (e : E X) : ITree E X := .vis e .ret

/-- Monadic bind: run `t`, then `f` on its result. -/
def ITree.bind (t : ITree E R) (f : R → ITree E S) : ITree E S :=
  match t.dtor with
  | .ret r => f r
  | .vis e k => .vis e fun a => (k a).bind f
  | .div => .div
partial_fixpoint

@[simp] theorem ITree.ret_bind (r : R) (f : R → ITree E S) : (ITree.ret r).bind f = f r := by
  rw [ITree.bind, ITree.dtor_ret]

@[simp] theorem ITree.vis_bind {X : Type} (e : E X) (k : X → ITree E R) (f : R → ITree E S) :
    (ITree.vis e k).bind f = .vis e fun a => (k a).bind f := by
  rw [ITree.bind, ITree.dtor_vis]

@[simp] theorem ITree.div_bind (f : R → ITree E S) : (ITree.div : ITree E R).bind f = .div := by
  rw [ITree.bind, ITree.dtor_div]

theorem ITree.bind_ret (t : ITree E R) : t.bind .ret = t := by
  refine ITree.bisim (fun x y => x = y.bind .ret) ?_ rfl
  rintro _ y rfl
  cases y <;> simp [ITree.dtor_ret, ITree.dtor_vis, ITree.dtor_div] <;> constructor

theorem ITree.bind_assoc {T : Type} (t : ITree E R) (f : R → ITree E S) (g : S → ITree E T) :
    (t.bind f).bind g = t.bind fun r => (f r).bind g := by
  refine ITree.bisim (fun x y => x = y ∨ ∃ t : ITree E R,
    x = (t.bind f).bind g ∧ y = t.bind fun r => (f r).bind g) ?_ (.inr ⟨t, rfl, rfl⟩)
  rintro x y (rfl | ⟨t, rfl, rfl⟩)
  · rw [← ITree.F.fmap_id x.dtor]
    exact ITree.F.rel_fmap _ _ _ _ fun _ => Or.inl rfl
  cases t <;> simp only [ITree.ret_bind, ITree.vis_bind, ITree.div_bind, ITree.dtor_vis]
  · rw [← ITree.F.fmap_id ((f _).bind g).dtor]
    exact ITree.F.rel_fmap _ _ _ _ fun _ => Or.inl rfl
  · exact .vis _ _ _ fun a => .inr ⟨_, rfl, rfl⟩
  · exact .div

instance : Monad (ITree E) where
  pure := ITree.ret
  bind := ITree.bind

instance : LawfulMonad (ITree E) := LawfulMonad.mk'
  (id_map := ITree.bind_ret)
  (pure_bind := ITree.ret_bind)
  (bind_assoc := ITree.bind_assoc)

/-- `bind` is monotone in both arguments, so `partial_fixpoint` accepts recursion through `do`. -/
instance : MonoBind (ITree E) where
  bind_mono_left {_ _ t₁ t₂ f} h := by
    refine ITree.approx_coind (fun x y => ∃ t₁ t₂, t₁ ⊑ t₂ ∧ x = t₁.bind f ∧ y = t₂.bind f) ?_
      ⟨t₁, t₂, h, rfl, rfl⟩
    rintro _ _ ⟨t₁, t₂, h, rfl, rfl⟩
    rw [ITree.approx_iff] at h
    rcases h with rfl | h
    · exact .inl (ITree.div_bind f ▸ ITree.bot_eq (E := E) ▸ bot_le _)
    cases t₁ <;> cases t₂ <;> simp only [ITree.dtor_ret, ITree.dtor_vis, ITree.dtor_div] at h <;>
      cases h
    · exact .inl PartialOrder.rel_refl
    · rename_i h
      simp only [ITree.vis_bind, ITree.dtor_vis]
      exact .inr (.vis _ _ _ fun a => .inl ⟨_, _, h a, rfl, rfl⟩)
    · exact .inl PartialOrder.rel_refl
  bind_mono_right {_ _ t f₁ f₂} h := by
    refine ITree.approx_coind (fun x y => ∃ t, x = t.bind f₁ ∧ y = t.bind f₂) ?_ ⟨t, rfl, rfl⟩
    rintro _ _ ⟨t, rfl, rfl⟩
    cases t <;> simp only [ITree.ret_bind, ITree.vis_bind, ITree.div_bind, ITree.dtor_vis]
    · exact .inl (h _)
    · exact .inr (.vis _ _ _ fun _ => .inl ⟨_, rfl, rfl⟩)
    · exact .inl PartialOrder.rel_refl

/-! ## 2. Events and traces -/

/-- An event that happened, with the answer the environment gave. -/
structure Event (E : Type → Type) where
  {X : Type}
  e : E X
  a : X

/-- A finite trace: the events so far, oldest first. -/
abbrev Trace (E : Type → Type) := List (Event E)

end
