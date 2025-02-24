import LoL.MProp.EffectObservations
import LoL.MProp.Instances

universe u v w

variable {m : Type u -> Type v} [Monad m] [LawfulMonad m] {α : Type u}
variable {l : Type u} [Preorder l]

section
variable [MProp m l]

def triple (pre : l) (c : m α) (post : α -> l) : Prop :=
  pre ≤ liftM (n := Cont l) c post

abbrev mtriple (pre : m PProp) (c : m α) (post : α -> m PProp) : Prop :=
  triple (MProp.μ pre) c (MProp.μ (m := m) ∘ post)

lemma mtriple_pure (pre : m PProp) (x : α) (post : α -> m PProp) :
  MProp.μ pre ≤ MProp.μ (post x) ->
  mtriple pre (pure x) post := by
    intros h; rw [mtriple, triple]; simp [liftM, lift_pure]; apply h
end

variable [MPropOrdered m l]

lemma mtriple_bind {β} (pre : m PProp) (x : m α) (cut : α -> m PProp)
  (f : α -> m β) (post : β -> m PProp) :
  mtriple pre x cut ->
  (∀ y, mtriple (cut y) (f y) post) ->
  mtriple pre (x >>= f) post := by
    intros hcut hpost
    simp [mtriple, triple, liftM, lift_bind]
    apply le_trans; apply hcut
    have h: monadLift x = MProp.lift x := by rfl
    simp [h, Bind.bind];
    apply Cont.monotone_lift; apply hpost

theorem Triple.forIn_list {α β}
  {xs : List α} {init : β} {f : α → β → m (ForInStep β)}
  (inv : List α → β → m PProp)
  (hstep : ∀ hd tl b,
    mtriple
      (inv (hd :: tl) b)
      (f hd b)
      (fun | .yield b' => inv tl b' | .done b' => inv [] b')) :
  mtriple (inv xs init) (forIn xs init f) (inv []) := by
    induction xs generalizing init
    { apply mtriple_pure; simp }
    simp only [List.forIn_cons]
    apply mtriple_bind; apply hstep; intros y
    cases y <;> simp <;> solve_by_elim [mtriple_pure, le_refl]
