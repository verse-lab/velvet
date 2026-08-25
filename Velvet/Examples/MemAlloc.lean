import Velvet

open Std.WP

namespace Velvet.Examples.MemAlloc

set_option autoImplicit true
set_option velvet.semantics.termination "partial"

@[reducible]
def addr := Int

@[reducible]
def path (h : addr → addr) (x : addr) (l : List addr) (y : addr) :=
  match l with
  | [] => x = y
  | a :: t => a ≠ 0 ∧ x = a ∧ path h (h a) t y

@[reducible]
def distinct (l : List addr) :=
  match l with
  | [] => True
  | a :: t => (∀ x, x ∈ t → x ≠ a) ∧ distinct t

@[reducible]
def distPath (h : addr → addr) (x : addr) (l : List addr) (y : addr) :=
  path h x l y ∧ distinct l

@[reducible]
def updateAt (f : addr → addr) (a v : addr) : addr → addr :=
  fun x => if x = a then v else f x

structure AllocResult where
  mem : addr
  next : addr → addr
  freeList : addr

def mem_alloc (block_size : addr → Nat) (size : Nat) (Ps : List addr)
    (next0 : addr → addr) (free0 : addr) : Option AllocResult := do
  let mut next := next0
  let mut free := free0
  if free = 0 then
    return { mem := 0, next := next, freeList := free }
  else if block_size free ≥ size then
    let res := free
    free := next free
    return { mem := res, next := next, freeList := free }
  else
    let mut q := free
    let mut p := next free
    while' p ≠ 0 ∧ block_size p < size
      invariant dist_inv : distPath next free Ps 0
      invariant reach_p : ∃ Qs, distPath next free Qs p ∧ ∀ a, a ∈ Qs → block_size a < size
      invariant p_next_q : p = next q
      invariant reach_q : ∃ Qs, distPath next free Qs q
      invariant q_nonzero : q ≠ 0
    do
      q := p
      p := next p
    if p ≠ 0 then
      next := updateAt next q (next p)
      return { mem := p, next := next, freeList := free }
    else
      return { mem := 0, next := next, freeList := free }

theorem path_append {h : addr → addr} {x y z : addr} {l1 l2 : List addr} :
    path h x l1 y → path h y l2 z → path h x (l1 ++ l2) z := by
  intro h1 h2
  induction l1 generalizing x with
  | nil => simp only [path] at h1; subst h1; exact h2
  | cons a t ih => rcases h1 with ⟨ha0, rfl, hrest⟩; exact ⟨ha0, rfl, ih hrest⟩

theorem path_append' {h : addr → addr} {x y : addr} {l1 l2 : List addr} :
    path h x (l1 ++ l2) y ↔ ∃ z, path h x l1 z ∧ path h z l2 y := by
  induction l1 generalizing x with
  | nil => simp [path]
  | cons a t ih =>
      simp only [path, List.cons_append]
      constructor
      · rintro ⟨ha0, rfl, hrest⟩
        rcases (ih.1 hrest) with ⟨z, hz1, hz2⟩
        exact ⟨z, ⟨ha0, rfl, hz1⟩, hz2⟩
      · rintro ⟨z, ⟨ha0, rfl, hz1⟩, hz2⟩
        exact ⟨ha0, rfl, ih.2 ⟨z, hz1, hz2⟩⟩

theorem path_prefix {h : addr → addr} {x y1 y2 : addr} {l1 l2 : List addr}
    (h1 : path h x l1 y1) (h2 : path h x l2 y2) : l1 <+: l2 ∨ l2 <+: l1 := by
  induction l1 generalizing x y1 l2 with
  | nil => left; exact ⟨l2, rfl⟩
  | cons a t ih =>
      cases l2 with
      | nil => right; exact ⟨a :: t, rfl⟩
      | cons b t2 =>
          rcases h1 with ⟨ha0, rfl, h1'⟩
          rcases h2 with ⟨hb0, hxb, h2'⟩
          subst hxb
          rcases ih h1' h2' with ⟨w, hw⟩ | ⟨w, hw⟩
          · left; exact ⟨w, by simp [hw]⟩
          · right; exact ⟨w, by simp [hw]⟩

theorem path_function {h : addr → addr} {x y1 y2 : addr} {l : List addr}
    (h1 : path h x l y1) (h2 : path h x l y2) : y1 = y2 := by
  induction l generalizing x y1 y2 with
  | nil => simp only [path] at h1 h2; subst h1; exact h2
  | cons a t ih =>
      rcases h1 with ⟨_, hxa, h1'⟩
      rcases h2 with ⟨_, hxb, h2'⟩
      rw [hxa] at hxb
      exact ih h1' (hxb ▸ h2')

theorem path_zero_mem {h : addr → addr} {x y : addr} {l : List addr}
    (hp : path h x l y) : 0 ∉ l := by
  induction l generalizing x with
  | nil => simp
  | cons a t ih =>
      rcases hp with ⟨ha0, rfl, hrest⟩
      intro hmem
      rcases List.mem_cons.mp hmem with hz | ht
      · exact ha0 hz.symm
      · exact ih hrest ht

theorem distinct_append {l1 l2 : List addr} :
    distinct (l1 ++ l2) ↔ distinct l1 ∧ distinct l2 ∧ ∀ x ∈ l1, x ∉ l2 := by
  induction l1 with
  | nil => unfold distinct; simp
  | cons a t ih =>
      constructor
      · intro h
        unfold distinct at h
        rcases h with ⟨hneq, hdt⟩
        rcases ih.1 hdt with ⟨hdt', hd2, hdisj⟩
        constructor
        · constructor
          · intro x hx
            exact hneq x (List.mem_append.mpr (Or.inl hx))
          · exact hdt'
        · constructor
          · exact hd2
          · intro x hx
            rcases (List.mem_cons.mp hx) with h | h
            · subst x
              intro ha
              exact (hneq a (List.mem_append.mpr (Or.inr ha))) rfl
            · exact hdisj x h
      · intro h
        rcases h with ⟨hdt, hd2, hdisj⟩
        rcases hdt with ⟨hneq, hdt'⟩
        unfold distinct
        constructor
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hneq x h
          · intro hxa
            exact hdisj a (by simp) (by simpa [hxa] using h)
        · exact ih.2 ⟨hdt', hd2, by intro x hx; exact hdisj x (by simp [hx])⟩

theorem path_update_of_not_mem {h : addr → addr} {x y u v : addr} {l : List addr}
    (hp : path h x l y) (hu : u ∉ l) : path (updateAt h u v) x l y := by
  induction l generalizing x y with
  | nil => exact hp
  | cons a t ih =>
      rcases hp with ⟨ha0, hxa, hrest⟩
      have hneq : a ≠ u := fun ha_u => hu (ha_u ▸ List.mem_cons_self ..)
      have hupd : updateAt h u v a = h a := by simp [updateAt, hneq]
      refine ⟨ha0, hxa, ?_⟩
      simpa [hupd] using ih hrest (fun hu' => hu (List.mem_cons_of_mem _ hu'))

theorem path_zero_unique (h : addr → addr) (x : addr) (l1 l2 : List addr) :
    path h x l1 0 → path h x l2 0 → l1 = l2 := by
  intro h1 h2
  induction l1 generalizing x l2 with
  | nil =>
      cases l2 with
      | nil => rfl
      | cons a t => rcases h2 with ⟨ha0, hxa, _⟩; subst h1; exact (ha0 hxa.symm).elim
  | cons a t ih =>
      cases l2 with
      | nil => rcases h1 with ⟨ha0, hxa, _⟩; subst h2; exact (ha0 hxa.symm).elim
      | cons b t2 =>
          rcases h1 with ⟨ha0, hxa, h1'⟩
          rcases h2 with ⟨hb0, hxb, h2'⟩
          rw [hxa] at hxb
          subst b
          rw [ih (h a) t2 h1' h2']

theorem path_split_at_p {h : addr → addr} {x p : addr} {Ps Qs : List addr}
    (hPs : path h x Ps 0) (hQs : path h x Qs p) (hp : p ≠ 0) : ∃ Rest, Ps = Qs ++ p :: Rest := by
  revert hPs hQs
  induction Qs generalizing x Ps with
  | nil =>
      intro hPs hQs
      simp only [path] at hQs
      cases Ps with
      | nil => simp only [path] at hPs; subst hQs hPs; exact (hp rfl).elim
      | cons a t => rcases hPs with ⟨ha0, rfl, _⟩; subst hQs; exact ⟨t, rfl⟩
  | cons b t ih =>
      intro hPs hQs
      rcases hQs with ⟨hb0, rfl, hQs'⟩
      cases Ps with
      | nil => simp only [path] at hPs; subst hPs; exact (hb0 rfl).elim
      | cons c u =>
          rcases hPs with ⟨hc0, hxc, hPs'⟩
          subst hxc
          obtain ⟨Rest, hRest⟩ := ih hPs' hQs'
          exact ⟨Rest, by simp [hRest]⟩

theorem find_in_split {α} {p : α → Bool} {l1 l2 : List α} {b : α}
    (h1 : ∀ x ∈ l1, p x = false) (h2 : p b = true) : (l1 ++ b :: l2).find? p = some b := by
  induction l1 with
  | nil => simp [h2]
  | cons a t ih =>
      simp only [List.cons_append, List.find?_cons]
      have ha : p a = false := h1 a (List.mem_cons_self ..)
      simp [ha, ih (fun x hx => h1 x (List.mem_cons_of_mem _ hx))]

theorem find?_eq_none_of_forall {α} {p : α → Bool} {l : List α}
    (h : ∀ a ∈ l, p a = false) : l.find? p = none := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      have ha : p a = false := h a (List.mem_cons_self ..)
      simp [List.find?, ha, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem path_update_skip {h : addr → addr} {x p q : addr} {Qs_q Rest : List addr}
    (h_path : path h x (Qs_q ++ [q] ++ p :: Rest) 0)
    (h_distinct : distinct (Qs_q ++ [q] ++ p :: Rest))
    (_h_link : p = h q)
    (hq : q ≠ 0) :
    path (updateAt h q (h p)) x (Qs_q ++ [q] ++ Rest) 0 := by
  obtain ⟨z, hz1, hz2⟩ := path_append'.mp h_path
  simp only [path] at hz2
  obtain ⟨_, hzp, htail⟩ := hz2
  rcases distinct_append.mp h_distinct with ⟨d1, d2, d3⟩
  rcases distinct_append.mp d1 with ⟨d11, d12, d13⟩
  have hq_not_Qs : q ∉ Qs_q := fun hmem => d13 q hmem (by simp)
  have hq_not_Rest : q ∉ Rest := fun hmem =>
    d3 q (List.mem_append.mpr (Or.inr (by simp))) (List.mem_cons_of_mem _ hmem)
  obtain ⟨qq, hqq1, hqq2⟩ := path_append'.mp hz1
  have hqqq : qq = q := by
    simp only [path] at hqq2
    exact hqq2.2.1
  rw [hqqq] at hqq1
  refine path_append'.mpr ⟨h p, ?_, ?_⟩
  · refine path_append'.mpr ⟨q, ?_, ?_⟩
    · exact path_update_of_not_mem hqq1 hq_not_Qs
    · exact ⟨hq, rfl, by simp [updateAt]⟩
  · exact path_update_of_not_mem htail hq_not_Rest

theorem erase_middle_unique {l1 l2 : List addr} {p : addr}
    (h : distinct (l1 ++ p :: l2)) : (l1 ++ p :: l2).erase p = l1 ++ l2 := by
  induction l1 with
  | nil => simp
  | cons a t ih =>
      rcases distinct_append.1 h with ⟨⟨ha_t, hdt⟩, hd2, hdisj⟩
      have : a ≠ p := fun hap => hdisj a (by simp) (hap ▸ List.mem_cons_self ..)
      simp [this, ih (distinct_append.2 ⟨hdt, hd2, fun x hx => hdisj x (List.mem_cons_of_mem _ hx)⟩)]

theorem distinct_erase_middle {l1 l2 : List addr} {p : addr}
    (h : distinct (l1 ++ p :: l2)) : distinct (l1 ++ l2) := by
  rcases distinct_append.1 h with ⟨hd1, hd2, hdisj⟩
  exact distinct_append.2 ⟨hd1, hd2.2, fun x hx hxl => hdisj x hx (List.Mem.tail (b := p) hxl)⟩

theorem path_split_at_q_p {h : addr → addr} {x q p : addr} {Ps Qsq : List addr}
    (hPs : path h x Ps 0) (hpQsq : path h x Qsq q) (hq : q ≠ 0) (hpq : p = h q) (hp : p ≠ 0) :
    ∃ Rest, Ps = Qsq ++ [q] ++ p :: Rest := by
  obtain ⟨R, hR⟩ := path_split_at_p hPs hpQsq hq
  subst hR
  obtain ⟨z, hz1, hz2⟩ := path_append'.mp hPs
  have hzq : z = q := path_function hz1 hpQsq
  rw [hzq] at hz2
  simp only [path] at hz2
  have hR0 : path h p R 0 := by rw [← hpq] at hz2; exact hz2.2.2
  cases R with
  | nil => simp only [path] at hR0; exact (hp hR0).elim
  | cons dd rr =>
      simp only [path] at hR0
      exact ⟨rr, by simp [hR0.2.1]⟩

theorem goal1 {block_size : addr → Nat} {size : Nat} {Ps : List addr} {next0 : addr → addr} {free0 : addr}
    (hdist : path next0 free0 Ps 0 ∧ distinct Ps) (hfree0 : free0 = 0) {b : addr}
    (hfind : List.find? (fun x => decide (size ≤ block_size x)) Ps = some b) :
    0 = b ∧ path next0 free0 (Ps.erase b) 0 ∧ distinct (Ps.erase b) := by
  cases Ps with
  | nil => simp at hfind
  | cons a t => rcases hdist.1 with ⟨ha0, hxa, _⟩; subst hfree0 hxa; exact (ha0 rfl).elim

theorem goal2 {block_size : addr → Nat} {size : Nat} {Ps : List addr} {next0 : addr → addr} {free0 : addr}
    (hdist : path next0 free0 Ps 0 ∧ distinct Ps) (hfree0 : free0 ≠ 0) (hblock : size ≤ block_size free0) {b : addr}
    (hfind : List.find? (fun x => decide (size ≤ block_size x)) Ps = some b) :
    free0 = b ∧ path next0 (next0 free0) (Ps.erase b) 0 ∧ distinct (Ps.erase b) := by
  cases Ps with
  | nil => rcases hdist.1 with rfl; exact (hfree0 rfl).elim
  | cons a t =>
      rcases hdist with ⟨⟨ha0, rfl, hpath⟩, ⟨hd_hd, hd_tl⟩⟩
      have hdec : decide (size ≤ block_size free0) = true := decide_eq_true hblock
      simp only [List.find?, hdec] at hfind
      injection hfind with hb
      subst hb
      simp [hpath, hd_tl]

theorem goal4 {block_size : addr → Nat} {size : Nat} {Ps : List addr} {next0 : addr → addr} {free0 : addr}
    (_hdist : path next0 free0 Ps 0 ∧ distinct Ps) (hfree0 : free0 ≠ 0) (hblock : ¬ size ≤ block_size free0) :
    ∃ Qs, (path next0 free0 Qs (next0 free0) ∧ distinct Qs) ∧ ∀ a ∈ Qs, block_size a < size :=
  ⟨[free0], ⟨⟨hfree0, rfl, rfl⟩, ⟨by simp, trivial⟩⟩, by simpa using Nat.lt_of_not_ge hblock⟩

theorem goal5 {block_size : addr → Nat} {size : Nat} {Ps : List addr} {next0 : addr → addr} {free0 : addr}
    (_hdist : path next0 free0 Ps 0 ∧ distinct Ps) (_hfree0 : free0 ≠ 0) (_hblock : ¬ size ≤ block_size free0) :
    ∃ Qs, path next0 free0 Qs free0 ∧ distinct Qs :=
  ⟨[], rfl, trivial⟩

theorem goal3 {block_size : addr → Nat} {size : Nat} {Ps : List addr} {next0 : addr → addr} {free0 : addr} {p : addr}
    (hdist_inv : path next0 free0 Ps 0 ∧ distinct Ps)
    (hreach_p : ∃ Qs, (path next0 free0 Qs p ∧ distinct Qs) ∧ ∀ a ∈ Qs, block_size a < size)
    (hloop : p ≠ 0 ∧ block_size p < size) :
    ∃ Qs, (path next0 free0 Qs (next0 p) ∧ distinct Qs) ∧ ∀ a ∈ Qs, block_size a < size := by
  rcases hreach_p with ⟨Qs, ⟨hpQs, hdQs⟩, hsmall⟩
  obtain ⟨Rest, hPs_eq⟩ := path_split_at_p hdist_inv.1 hpQs hloop.1
  have hp_not_Qs : p ∉ Qs := by
    have hdistPs : distinct (Qs ++ p :: Rest) := hPs_eq ▸ hdist_inv.2
    rcases distinct_append.1 hdistPs with ⟨_, _, hdisj⟩
    exact fun hmem => hdisj p hmem (by simp)
  refine ⟨Qs ++ [p], ⟨path_append hpQs ⟨hloop.1, rfl, rfl⟩, ?_⟩, ?_⟩
  · rw [distinct_append]
    refine ⟨hdQs, ⟨by simp, trivial⟩, ?_⟩
    intro x hx hp_mem
    simp only [List.mem_singleton] at hp_mem
    subst hp_mem
    exact hp_not_Qs hx
  · intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hsmall a ha
    · simp only [List.mem_singleton] at ha; subst ha; exact hloop.2

theorem goal6 {block_size : addr → Nat} {size : Nat} {Ps : List addr} {next0 : addr → addr} {free0 : addr} {q p : addr}
    (dist_inv : path next0 free0 Ps 0 ∧ distinct Ps)
    (reach_p : ∃ Qs, (path next0 free0 Qs p ∧ distinct Qs) ∧ ∀ a ∈ Qs, block_size a < size)
    (p_next_q : p = next0 q)
    (reach_q : ∃ Qs, path next0 free0 Qs q ∧ distinct Qs)
    (q_nonzero : q ≠ 0)
    (h_done_with : ¬(p ≠ 0 ∧ block_size p < size))
    (hp : p ≠ 0) {b : addr}
    (hfind : List.find? (fun x => decide (size ≤ block_size x)) Ps = some b) :
    p = b ∧ path (updateAt next0 q (next0 p)) free0 (Ps.erase b) 0 ∧ distinct (Ps.erase b) := by
  obtain ⟨Qsp, ⟨hQsp_path, _⟩, hQsp_small⟩ := reach_p
  obtain ⟨Qsq, hQsq_path, _⟩ := reach_q
  obtain ⟨R, hPs_eq⟩ := path_split_at_q_p dist_inv.1 hQsq_path q_nonzero p_next_q hp
  have hdistP : distinct (Qsq ++ [q] ++ p :: R) := hPs_eq ▸ dist_inv.2
  have hpre : Qsq <+: Qsp := by
    rcases path_prefix hQsq_path hQsp_path with h | ⟨w, hw⟩
    · exact h
    · exfalso
      subst hw
      obtain ⟨z, hz1, hz2⟩ := path_append'.mp hQsq_path
      have hzp : z = p := path_function hz1 hQsp_path
      rw [hzp] at hz2
      have hpB : p ∈ p :: R := List.mem_cons_self ..
      have hpA : p ∈ Qsp ++ w ++ [q] := by
        cases w with
        | nil => simp only [path] at hz2; exact List.mem_append_right _ (by simpa using hz2)
        | cons dd ww =>
            simp only [path] at hz2
            exact List.mem_append_left _ (List.mem_append_right Qsp (List.mem_cons.mpr (Or.inl hz2.2.1)))
      exact (distinct_append.mp hdistP).2.2 p hpA hpB
  have hqp : q ≠ p := by
    intro he; subst he
    exact (distinct_append.mp hdistP).2.2 _
      (List.mem_append_right _ (List.mem_cons_self ..)) (List.mem_cons_self ..)
  obtain ⟨w, hw⟩ := hpre
  have hQsq_sub : ∀ a ∈ Qsq, block_size a < size := fun a ha =>
    hQsp_small a (hw ▸ List.mem_append_left _ ha)
  have hq_mem_Qsp : q ∈ Qsp := by
    cases w with
    | nil => exfalso; rw [← hw, List.append_nil] at hQsp_path; exact hqp (path_function hQsq_path hQsp_path)
    | cons dd ww =>
        rw [← hw] at hQsp_path
        obtain ⟨z, hz1, hz2⟩ := path_append'.mp hQsp_path
        have hzq : z = q := path_function hz1 hQsq_path
        rw [hzq] at hz2
        simp only [path] at hz2
        rw [← hw]
        exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl hz2.2.1))
  have hfalse : ∀ a ∈ Qsq ++ [q], (fun x => decide (size ≤ block_size x)) a = false := by
    intro a ha
    have hsmall : block_size a < size := by
      rcases List.mem_append.mp ha with h | h
      · exact hQsq_sub a h
      · have haq : a = q := List.mem_singleton.mp h
        exact haq ▸ hQsp_small q hq_mem_Qsp
    exact decide_eq_false_iff_not.mpr (Nat.not_le.mpr hsmall)
  have htrue : (fun x => decide (size ≤ block_size x)) p = true :=
    decide_eq_true_iff.mpr (Nat.le_of_not_gt (fun hc => h_done_with ⟨hp, hc⟩))
  have hfindP : List.find? (fun x => decide (size ≤ block_size x)) ((Qsq ++ [q]) ++ p :: R) = some p :=
    find_in_split hfalse htrue
  have heq : List.find? (fun x => decide (size ≤ block_size x)) Ps = some p := by rw [hPs_eq, hfindP]
  rw [heq] at hfind
  injection hfind with hb_eq
  subst hb_eq
  have hd1 : path next0 free0 (Qsq ++ [q] ++ p :: R) 0 := hPs_eq ▸ dist_inv.1
  rw [hPs_eq, erase_middle_unique hdistP]
  exact ⟨rfl, path_update_skip hd1 hdistP p_next_q q_nonzero, distinct_erase_middle hdistP⟩

theorem goal7 {block_size : addr → Nat} {size : Nat} {Ps : List addr} {next0 : addr → addr} {free0 : addr} {q p : addr}
    (dist_inv : path next0 free0 Ps 0 ∧ distinct Ps)
    (reach_p : ∃ Qs, (path next0 free0 Qs p ∧ distinct Qs) ∧ ∀ a ∈ Qs, block_size a < size)
    (_p_next_q : p = next0 q)
    (_reach_q : ∃ Qs, path next0 free0 Qs q ∧ distinct Qs)
    (_q_nonzero : q ≠ 0)
    (_h_done_with : ¬(p ≠ 0 ∧ block_size p < size))
    (hcond : ¬(p ≠ 0)) {b : addr}
    (hfind : List.find? (fun x => decide (size ≤ block_size x)) Ps = some b) :
    0 = b ∧ path next0 free0 (Ps.erase b) 0 ∧ distinct (Ps.erase b) := by
  have hp0 : p = 0 := by grind
  rcases reach_p with ⟨Qs, ⟨hpQs, _⟩, hsmall⟩
  have hQs_eq_Ps : Qs = Ps := path_zero_unique next0 free0 Qs Ps (hp0 ▸ hpQs) dist_inv.1
  have hnone : List.find? (fun x => decide (size ≤ block_size x)) Ps = none := by
    apply find?_eq_none_of_forall
    intro a ha
    simp [Nat.not_le_of_gt (hsmall a (hQs_eq_Ps ▸ ha))]
  rw [hnone] at hfind
  nomatch hfind

theorem mem_alloc_correct (block_size : addr → Nat) (size : Nat) (Ps : List addr)
    (next0 : addr → addr) (free0 : addr) :
    Triple (mem_alloc block_size size Ps next0 free0)
      (distPath next0 free0 Ps 0)
      (fun r => ∀ b, List.find? (fun x => decide (block_size x ≥ size)) Ps = some b →
          r.mem = b ∧ distPath r.next r.freeList (List.erase Ps b) 0)
      (fun (_ : Unit) => True) := by
  vcgen_ [mem_alloc] with try finish
  all_goals first
    | apply goal1 <;> assumption
    | apply goal2 <;> assumption
    | apply goal3 <;> assumption
    | apply goal4 <;> assumption
    | apply goal5 <;> assumption
    | apply goal6 <;> assumption
    | apply goal7 <;> assumption

end Velvet.Examples.MemAlloc
