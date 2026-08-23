import Velvet2.Syntax
import Velvet2.VCGen.Frontend

open Std.Internal.Do

namespace Velvet2.Examples.MemAlloc

set_option autoImplicit true
set_option velvet.semantics.termination "partial"

@[reducible]
def addr := Int

/-- `path h x l y`: following `h` from `x` through the addresses in `l` reaches `y`. -/
@[reducible]
def path (h : addr → addr) (x : addr) (l : List addr) (y : addr) :=
  match l with
  | [] => x = y
  | a :: t => a ≠ 0 ∧ x = a ∧ path h (h a) t y

/-- `distinct l`: every element of `l` is distinct. -/
@[reducible]
def distinct (l : List addr) :=
  match l with
  | [] => True
  | a :: t => (∀ x, x ∈ t → x ≠ a) ∧ distinct t

/-- A path whose addresses are all distinct (and hence acyclic). -/
@[reducible]
def distPath (h : addr → addr) (x : addr) (l : List addr) (y : addr) :=
  path h x l y ∧ distinct l

/-- Pointwise function update (core-Lean substitute for `Function.update`). -/
@[reducible]
def updateAt (f : addr → addr) (a v : addr) : addr → addr :=
  fun x => if x = a then v else f x

/-- The result of an allocation. -/
structure AllocResult where
  mem : addr
  next : addr → addr
  freeList : addr

-----------------------------------------------------------------------------------
--- The program
-----------------------------------------------------------------------------------

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

-----------------------------------------------------------------------------------
--- HELPER LEMMAS
-----------------------------------------------------------------------------------

theorem path_append {h : addr → addr} {x y z : addr} {l1 l2 : List addr} :
    path h x l1 y → path h y l2 z → path h x (l1 ++ l2) z := by
  intro h1 h2
  induction l1 generalizing x y z with
  | nil => unfold path at h1; simpa [h1] using h2
  | cons a t ih =>
      unfold path at h1 ⊢
      rcases h1 with ⟨ha0, hxa, hrest⟩
      refine ⟨ha0, hxa, ?_⟩
      exact ih hrest h2

theorem path_append' {h : addr → addr} {x y : addr} {l1 l2 : List addr} :
    path h x (l1 ++ l2) y ↔ ∃ z, path h x l1 z ∧ path h z l2 y := by
  induction l1 generalizing x with
  | nil => unfold path; simp
  | cons a t ih =>
      constructor
      · intro h
        unfold path at h
        rcases h with ⟨ha0, hxa, hrest⟩
        rcases (@ih (h a)).1 hrest with ⟨z, hz1, hz2⟩
        exact ⟨z, ⟨ha0, hxa, hz1⟩, hz2⟩
      · intro h
        rcases h with ⟨z, hz, hz'⟩
        unfold path
        unfold path at hz
        rcases hz with ⟨ha0, hxa, hrest⟩
        exact ⟨ha0, hxa, (@ih (h a)).2 ⟨z, hrest, hz'⟩⟩

theorem path_prefix {h : addr → addr} {x y1 y2 : addr} {l1 l2 : List addr}
    (h1 : path h x l1 y1) (h2 : path h x l2 y2) : l1 <+: l2 ∨ l2 <+: l1 := by
  induction l1 generalizing x y1 l2 with
  | nil => left; exact ⟨l2, rfl⟩
  | cons a t ih =>
      cases l2 with
      | nil => right; exact ⟨a :: t, rfl⟩
      | cons b t2 =>
          unfold path at h1 h2
          rcases h1 with ⟨ha0, hxa, h1'⟩
          rcases h2 with ⟨hb0, hxb, h2'⟩
          rw [hxa] at hxb
          subst b
          rcases ih h1' h2' with h | h
          · left; rcases h with ⟨w, hw⟩; exact ⟨w, by simp [hw]⟩
          · right; rcases h with ⟨w, hw⟩; exact ⟨w, by simp [hw]⟩

theorem path_function {h : addr → addr} {x y1 y2 : addr} {l : List addr}
    (h1 : path h x l y1) (h2 : path h x l y2) : y1 = y2 := by
  induction l generalizing x y1 y2 with
  | nil => unfold path at h1 h2; rw [h1] at h2; exact h2
  | cons a t ih =>
      unfold path at h1 h2
      rcases h1 with ⟨_, hxa, h1'⟩
      rcases h2 with ⟨_, hxb, h2'⟩
      rw [hxa] at hxb
      exact ih h1' (hxb ▸ h2')

theorem path_zero_mem {h : addr → addr} {x y : addr} {l : List addr}
    (hp : path h x l y) : 0 ∉ l := by
  induction l generalizing x y with
  | nil => simp
  | cons a t ih =>
      unfold path at hp
      rcases hp with ⟨ha0, _hxa, hrest⟩
      intro hmem
      rcases (List.mem_cons.mp hmem) with hz | ht
      · exact ha0 hz.symm
      · exact (ih hrest) ht

theorem path_nonzero {h : addr → addr} {x y : addr} {l : List addr}
    (hp : path h x l y) : ∀ a ∈ l, a ≠ 0 := by
  intro a ha ha0
  exact path_zero_mem hp (ha0 ▸ ha)

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
  | nil => unfold path at hp ⊢; exact hp
  | cons a t ih =>
      unfold path at hp ⊢
      rcases hp with ⟨ha0, hxa, hrest⟩
      have hneq : a ≠ u := by
        intro ha_u
        exact hu (by simpa [ha_u])
      have hupd : updateAt h u v a = h a := by
        unfold updateAt; simp [hneq]
      refine ⟨ha0, hxa, ?_⟩
      simpa [hupd] using @ih (h a) y hrest (by intro hu'; exact hu (by simp [hu']))

theorem path_zero_unique (h : addr → addr) (x : addr) (l1 l2 : List addr) :
    path h x l1 0 → path h x l2 0 → l1 = l2 := by
  intro h1 h2
  induction l1 generalizing x l2 with
  | nil =>
      cases l2 with
      | nil => rfl
      | cons a t =>
          unfold path at h1 h2
          rcases h2 with ⟨ha0, hxa, _h⟩
          exact (ha0 (hxa.symm.trans h1)).elim
  | cons a t ih =>
      cases l2 with
      | nil =>
          unfold path at h1 h2
          rcases h1 with ⟨ha0, hxa, _h⟩
          exact (ha0 (hxa.symm.trans h2)).elim
      | cons b t2 =>
          unfold path at h1 h2
          rcases h1 with ⟨ha0, hxa, h1'⟩
          rcases h2 with ⟨hb0, hxb, h2'⟩
          rw [hxa] at hxb
          subst b
          have ht := ih (h a) t2 h1' h2'
          rw [ht]

theorem path_split_at_p {h : addr → addr} {x p : addr} {Ps Qs : List addr}
    (hPs : path h x Ps 0) (hQs : path h x Qs p) (hp : p ≠ 0) : ∃ Rest, Ps = Qs ++ p :: Rest := by
  revert hPs hQs
  induction Qs generalizing x Ps with
  | nil =>
      intro hPs hQs
      simp only [path] at hQs
      cases Ps with
      | nil =>
          simp only [path] at hPs
          rw [hQs] at hPs
          exact absurd hPs hp
      | cons a t =>
          simp only [path] at hPs
          obtain ⟨ha0, hxa, _⟩ := hPs
          refine ⟨t, ?_⟩
          have hap : a = p := hxa.symm.trans hQs
          simp [hap]
  | cons b t ih =>
      intro hPs hQs
      simp only [path] at hQs
      obtain ⟨hb0, hxb, hQs'⟩ := hQs
      cases Ps with
      | nil =>
          simp only [path] at hPs
          rw [hxb] at hPs
          exact absurd hPs hb0
      | cons c u =>
          simp only [path] at hPs
          obtain ⟨hc0, hxc, hPs'⟩ := hPs
          have hbc : b = c := hxb.symm.trans hxc
          have hu' : path h (h b) u 0 := by rw [hbc]; exact hPs'
          obtain ⟨Rest, hRest⟩ := ih hu' hQs'
          exact ⟨Rest, by rw [hbc]; simp [hRest]⟩

theorem find_in_split {α} {p : α → Bool} {l1 l2 : List α} {b : α}
    (h1 : ∀ x ∈ l1, p x = false) (h2 : p b = true) : (l1 ++ b :: l2).find? p = some b := by
  induction l1 with
  | nil => simp [List.find?, h2]
  | cons a t ih =>
      simp only [List.cons_append, List.find?_cons]
      have ha : p a = false := h1 a (by simp)
      simp [ha, ih (by intro x hx; exact h1 x (by simp [hx]))]

theorem find?_eq_none_of_forall {α} {p : α → Bool} {l : List α}
    (h : ∀ a ∈ l, p a = false) : l.find? p = none := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      have ha : p a = false := h a (by simp)
      simp [List.find?, ha, ih (by intro x hx; exact h x (by simp [hx]))]

theorem path_prefix_of_path_to_zero {h : addr → addr} {x y : addr} {l1 l2 : List addr} :
    path h x l1 y → path h x l2 0 → y ≠ 0 → ∃ t, l2 = l1 ++ y :: t := by
  intro h1 h2 hy
  revert h1 h2
  induction l1 generalizing x l2 with
  | nil =>
      intro h1 h2
      simp only [path] at h1
      cases l2 with
      | nil =>
          simp only [path] at h2
          rw [h1] at h2
          exact absurd h2 hy
      | cons a t =>
          simp only [path] at h2
          obtain ⟨ha0, hxa, _⟩ := h2
          refine ⟨t, ?_⟩
          have hay : a = y := hxa.symm.trans h1
          simp [hay]
  | cons b t ih =>
      intro h1 h2
      simp only [path] at h1
      obtain ⟨hb0, hxb, h1'⟩ := h1
      cases l2 with
      | nil =>
          simp only [path] at h2
          rw [hxb] at h2
          exact absurd h2 hb0
      | cons c u =>
          simp only [path] at h2
          obtain ⟨hc0, hxc, h2'⟩ := h2
          have hbc : b = c := hxb.symm.trans hxc
          have hu' : path h (h b) u 0 := by rw [hbc]; exact h2'
          obtain ⟨t2, ht2⟩ := ih h1' hu'
          refine ⟨t2, ?_⟩
          rw [hbc]
          simp [ht2]

theorem path_update_skip {h : addr → addr} {x p q : addr} {Qs_q Rest : List addr}
    (h_path : path h x (Qs_q ++ [q] ++ p :: Rest) 0)
    (h_distinct : distinct (Qs_q ++ [q] ++ p :: Rest))
    (h_link : p = h q)
    (hq : q ≠ 0) :
    path (updateAt h q (h p)) x (Qs_q ++ [q] ++ Rest) 0 := by
  obtain ⟨z, hz1, hz2⟩ := path_append'.mp h_path
  simp only [path] at hz2
  obtain ⟨_, hzp, htail⟩ := hz2
  obtain ⟨d1, d2, d3⟩ := distinct_append.mp h_distinct
  obtain ⟨d11, d12, d13⟩ := distinct_append.mp d1
  have hq_not_Qs : q ∉ Qs_q := fun hmem =>
    d13 q hmem (by simp)
  have hq_not_Rest : q ∉ Rest := fun hmem =>
    d3 q (List.mem_append.mpr (Or.inr (by simp))) (List.mem_cons_of_mem _ hmem)
  obtain ⟨qq, hqq1, hqq2⟩ := path_append'.mp hz1
  have hqqq : qq = q := by
    simp only [path, List.cons_append] at hqq2
    exact hqq2.2.1
  rw [hqqq] at hqq1
  refine path_append'.mpr ⟨h p, ?_, ?_⟩
  · refine path_append'.mpr ⟨q, ?_, ?_⟩
    · exact path_update_of_not_mem hqq1 hq_not_Qs
    · exact ⟨hq, rfl, by simp [updateAt]⟩
  · exact path_update_of_not_mem htail hq_not_Rest

theorem erase_middle_unique {l1 l2 : List addr} {p : addr}
    (h : distinct (l1 ++ p :: l2)) : (l1 ++ p :: l2).erase p = l1 ++ l2 := by
  induction l1 generalizing l2 with
  | nil => simp [List.erase_cons_head]
  | cons a t ih =>
      unfold distinct at h
      simp only [List.cons_append, List.erase_cons] at h ⊢
      rcases h with ⟨hneq, hdt⟩
      have hne : a ≠ p := by
        intro hpa
        exact hneq p (by simp) hpa.symm
      by_cases hpa : a = p
      · exact False.elim (hne hpa)
      · simp [hpa, ih hdt]

theorem distinct_erase_middle {l1 l2 : List addr} {p : addr}
    (h : distinct (l1 ++ p :: l2)) : distinct (l1 ++ l2) := by
  rcases distinct_append.1 h with ⟨hd1, hd2, hdisj⟩
  have hd2' : distinct l2 := by
    unfold distinct at hd2
    exact hd2.2
  apply distinct_append.2
  constructor
  · exact hd1
  constructor
  · exact hd2'
  · intro x hx hxl
    exact hdisj x hx (List.Mem.tail (b := p) hxl)

theorem path_split_at_q_p {h : addr → addr} {x q p : addr} {Ps Qsq : List addr}
    (hPs : path h x Ps 0) (hpQsq : path h x Qsq q) (hq : q ≠ 0) (hpq : p = h q) (hp : p ≠ 0) :
    ∃ Rest, Ps = Qsq ++ [q] ++ p :: Rest := by
  obtain ⟨R, hR⟩ := path_split_at_p hPs hpQsq hq
  subst hR
  obtain ⟨z, hz1, hz2⟩ := path_append'.mp hPs
  have hzq : z = q := path_function hz1 hpQsq
  rw [hzq] at hz2
  simp only [path, List.cons_append] at hz2
  have hR0 : path h p R 0 := by
    rw [← hpq] at hz2
    exact hz2.2.2
  cases R with
  | nil =>
      simp only [path] at hR0
      exact absurd hR0 hp
  | cons dd rr =>
      simp only [path] at hR0
      have hdd : p = dd := hR0.2.1
      refine ⟨rr, ?_⟩
      simp [List.cons_append, hdd]

theorem goal1 {block_size : addr → Nat} {size : Nat} {Ps : List addr} {next0 : addr → addr} {free0 : addr}
    (hdist : path next0 free0 Ps 0 ∧ distinct Ps) (hfree0 : free0 = 0) {b : addr}
    (hfind : List.find? (fun x => decide (size ≤ block_size x)) Ps = some b) :
    0 = b ∧ path next0 free0 (Ps.erase b) 0 ∧ distinct (Ps.erase b) := by
  have hPs : Ps = [] := by
    cases Ps with
    | nil => rfl
    | cons a t =>
        unfold path at hdist
        rcases hdist.1 with ⟨ha0, hxa, _⟩
        rw [hfree0] at hxa
        exact (ha0 hxa.symm).elim
  subst Ps
  have hfalse : False := by simpa [List.find?] using hfind
  exact hfalse.elim

theorem goal2 {block_size : addr → Nat} {size : Nat} {Ps : List addr} {next0 : addr → addr} {free0 : addr}
    (hdist : path next0 free0 Ps 0 ∧ distinct Ps) (hfree0 : free0 ≠ 0) (hblock : size ≤ block_size free0) {b : addr}
    (hfind : List.find? (fun x => decide (size ≤ block_size x)) Ps = some b) :
    free0 = b ∧ path next0 (next0 free0) (Ps.erase b) 0 ∧ distinct (Ps.erase b) := by
  cases Ps with
  | nil => unfold path at hdist; exact (hfree0 hdist.1).elim
  | cons a t =>
      unfold path at hdist
      rcases hdist.1 with ⟨ha0, hxa, hrest⟩
      have ha_eq : a = free0 := hxa.symm
      subst a
      have hfind' : List.find? (fun x => decide (size ≤ block_size x)) (free0 :: t) = some free0 := by
        simp [hblock]
      have hsome : some free0 = some b := by
        rw [← hfind']; exact hfind
      have hfb : free0 = b := by injection hsome
      subst b
      refine ⟨rfl, ?_, ?_⟩
      · simpa [List.erase_cons_head] using hrest
      · have hd : distinct t := by
          unfold distinct at hdist
          exact hdist.2.2
        simpa [List.erase_cons_head] using hd

theorem goal4 {block_size : addr → Nat} {size : Nat} {Ps : List addr} {next0 : addr → addr} {free0 : addr}
    (hdist : path next0 free0 Ps 0 ∧ distinct Ps) (hfree0 : free0 ≠ 0) (hblock : ¬ size ≤ block_size free0) :
    ∃ Qs, (path next0 free0 Qs (next0 free0) ∧ distinct Qs) ∧ ∀ a ∈ Qs, block_size a < size := by
  refine ⟨[free0], ?_, ?_⟩
  · constructor
    · unfold path; simp [hfree0]
    · unfold distinct; simp
  · intro a ha
    simp only [List.mem_singleton] at ha
    subst a
    exact Nat.lt_of_not_ge hblock

theorem goal5 {block_size : addr → Nat} {size : Nat} {Ps : List addr} {next0 : addr → addr} {free0 : addr}
    (hdist : path next0 free0 Ps 0 ∧ distinct Ps) (hfree0 : free0 ≠ 0) (hblock : ¬ size ≤ block_size free0) :
    ∃ Qs, path next0 free0 Qs free0 ∧ distinct Qs := by
  refine ⟨[], ?_, ?_⟩
  · rfl
  · unfold distinct; simp

theorem goal3 {block_size : addr → Nat} {size : Nat} {Ps : List addr} {next0 : addr → addr} {free0 : addr} {p : addr}
    (hdist_inv : path next0 free0 Ps 0 ∧ distinct Ps)
    (hreach_p : ∃ Qs, (path next0 free0 Qs p ∧ distinct Qs) ∧ ∀ a ∈ Qs, block_size a < size)
    (hloop : p ≠ 0 ∧ block_size p < size) :
    ∃ Qs, (path next0 free0 Qs (next0 p) ∧ distinct Qs) ∧ ∀ a ∈ Qs, block_size a < size := by
  rcases hreach_p with ⟨Qs, ⟨hpQs, hdQs⟩, hsmall⟩
  have hp_not_Qs : p ∉ Qs := by
    intro hpQ
    rcases path_split_at_p hdist_inv.1 hpQs hloop.1 with ⟨Rest, hPs_eq⟩
    have hdistPs : distinct (Qs ++ p :: Rest) := by simpa [hPs_eq] using hdist_inv.2
    rcases distinct_append.1 hdistPs with ⟨_, _, hdisj⟩
    exact hdisj p hpQ (by simp)
  refine ⟨Qs ++ [p], ?_, ?_⟩
  · constructor
    · apply path_append hpQs
      unfold path; simp [hloop.1]
    · apply distinct_append.2
      constructor
      · exact hdQs
      constructor
      · unfold distinct; simp
      · intro x hx hmem
        have hxp : x = p := by simpa [List.mem_singleton] using hmem
        exact hp_not_Qs (hxp ▸ hx)
  · intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with h | h
    · exact hsmall a h
    · subst a; exact hloop.2

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
  -- Ps splits as Qsq ++ [q] ++ p :: R: up to q, along q, then the chosen block p
  obtain ⟨R, hPs_eq⟩ := path_split_at_q_p dist_inv.1 hQsq_path q_nonzero p_next_q hp
  have hdistP : distinct (Qsq ++ [q] ++ p :: R) := by
    rw [← hPs_eq]
    exact dist_inv.2
  -- Qsq must be a prefix of Qsp; in the reverse case p occurs twice in Ps
  have hpre : Qsq <+: Qsp := by
    rcases path_prefix hQsq_path hQsp_path with h | h
    · exact h
    · exfalso
      obtain ⟨w, hw⟩ := h
      subst hw
      obtain ⟨z, hz1, hz2⟩ := path_append'.mp hQsq_path
      have hzp : z = p := path_function hz1 hQsp_path
      rw [hzp] at hz2
      have hpB : p ∈ p :: R := List.mem_cons_self ..
      have hpA : p ∈ Qsp ++ w ++ [q] := by
        cases w with
        | nil =>
            simp only [path] at hz2
            exact List.mem_append_right _ (by simpa using hz2)
        | cons dd ww =>
            simp only [path] at hz2
            exact List.mem_append_left _ (List.mem_append_right Qsp (List.mem_cons.mpr (Or.inl hz2.2.1)))
      exact (distinct_append.mp hdistP).2.2 p hpA hpB
  -- q ≠ p: otherwise p occurs twice in the distinct list Ps
  have hqp : q ≠ p := by
    intro he
    subst he
    exact (distinct_append.mp hdistP).2.2 _
      (List.mem_append_right _ (List.mem_cons_self ..)) (List.mem_cons_self ..)
  obtain ⟨w, hw⟩ := hpre
  -- every node skipped before p is too small
  have hQsq_sub : ∀ a ∈ Qsq, block_size a < size := fun a ha =>
    hQsp_small a (by rw [← hw]; exact List.mem_append_left _ ha)
  have hq_mem_Qsp : q ∈ Qsp := by
    cases w with
    | nil =>
        exfalso
        rw [← hw, List.append_nil] at hQsp_path
        exact hqp (path_function hQsq_path hQsp_path)
    | cons dd ww =>
        rw [← hw] at hQsp_path
        obtain ⟨z, hz1, hz2⟩ := path_append'.mp hQsp_path
        have hzq : z = q := path_function hz1 hQsq_path
        rw [hzq] at hz2
        simp only [path, List.cons_append] at hz2
        rw [← hw]
        exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl hz2.2.1))
  have hq_small : block_size q < size := hQsp_small q hq_mem_Qsp

  have hfalse : ∀ a ∈ Qsq ++ [q], (fun x => decide (size ≤ block_size x)) a = false := by
    intro a ha
    have hsmall : block_size a < size := by
      rcases List.mem_append.mp ha with h | h
      · exact hQsq_sub a h
      · have haq : a = q := List.mem_singleton.mp h
        rw [haq]
        exact hq_small
    exact decide_eq_false_iff_not.mpr (Nat.not_le.mpr hsmall)
  have htrue : (fun x => decide (size ≤ block_size x)) p = true := by
    have hnlt : ¬ (block_size p < size) := fun hc => h_done_with ⟨hp, hc⟩
    exact decide_eq_true_iff.mpr (Nat.le_of_not_gt hnlt)
  have hfindP : List.find? (fun x => decide (size ≤ block_size x)) ((Qsq ++ [q]) ++ p :: R) = some p :=
    find_in_split hfalse htrue
  have heq : List.find? (fun x => decide (size ≤ block_size x)) Ps = some p := by
    rw [hPs_eq, hfindP]
  rw [heq] at hfind
  injection hfind with hb_eq
  subst hb_eq
  refine ⟨rfl, ?_, ?_⟩
  · have hd1 : path next0 free0 (Qsq ++ [q] ++ p :: R) 0 := by
      rw [← hPs_eq]
      exact dist_inv.1
    rw [hPs_eq, erase_middle_unique hdistP]
    exact path_update_skip hd1 hdistP p_next_q q_nonzero
  · rw [hPs_eq, erase_middle_unique hdistP]
    exact distinct_erase_middle hdistP

theorem goal7 {block_size : addr → Nat} {size : Nat} {Ps : List addr} {next0 : addr → addr} {free0 : addr} {q p : addr}
    (dist_inv : path next0 free0 Ps 0 ∧ distinct Ps)
    (reach_p : ∃ Qs, (path next0 free0 Qs p ∧ distinct Qs) ∧ ∀ a ∈ Qs, block_size a < size)
    (p_next_q : p = next0 q)
    (reach_q : ∃ Qs, path next0 free0 Qs q ∧ distinct Qs)
    (q_nonzero : q ≠ 0)
    (h_done_with : ¬(p ≠ 0 ∧ block_size p < size))
    (hcond : ¬(p ≠ 0)) {b : addr}
    (hfind : List.find? (fun x => decide (size ≤ block_size x)) Ps = some b) :
    0 = b ∧ path next0 free0 (Ps.erase b) 0 ∧ distinct (Ps.erase b) := by
  have hp0 : p = 0 := by
    by_cases h : p = 0
    · exact h
    · exfalso
      exact hcond h
  rcases reach_p with ⟨Qs, ⟨hpQs, hdQs⟩, hsmall⟩
  have hQs_eq_Ps : Qs = Ps := by
    rw [hp0] at hpQs
    exact path_zero_unique next0 free0 Qs Ps hpQs dist_inv.1
  subst Qs
  have hnone : List.find? (fun x => decide (size ≤ block_size x)) Ps = none := by
    apply find?_eq_none_of_forall
    intro a ha
    rw [decide_eq_false_iff_not]
    exact Nat.not_le_of_gt (hsmall a ha)
  have hcontra : none = some b := by simpa [hnone] using hfind
  nomatch hcontra

-----------------------------------------------------------------------------------
--- The actual verification
-----------------------------------------------------------------------------------

theorem mem_alloc_correct (block_size : addr → Nat) (size : Nat) (Ps : List addr)
    (next0 : addr → addr) (free0 : addr) :
    Triple (mem_alloc block_size size Ps next0 free0)
      (distPath next0 free0 Ps 0)
      (fun r => ∀ b, List.find? (fun x => decide (block_size x ≥ size)) Ps = some b →
          r.mem = b ∧ distPath r.next r.freeList (List.erase Ps b) 0)
      True := by
  vcgen_ [mem_alloc] with try finish
  all_goals first
    | apply goal1 <;> assumption
    | apply goal2 <;> assumption
    | apply goal3 <;> assumption
    | apply goal4 <;> assumption
    | apply goal5 <;> assumption
    | apply goal6 <;> assumption
    | apply goal7 <;> assumption

end Velvet2.Examples.MemAlloc
