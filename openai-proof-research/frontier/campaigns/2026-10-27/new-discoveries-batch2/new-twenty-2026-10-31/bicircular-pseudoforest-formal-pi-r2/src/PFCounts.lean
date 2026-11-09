import G2

namespace Bicir
open Relation

variable {g : Gr}

/-- Component-wise pseudoforest predicate: every `F`-component carries at most
as many `F`-edges as vertices. -/
noncomputable def IsPF (g : Gr) (F : Finset (Fin g.m)) : Prop :=
  ∀ x : Fin g.v, eIn g F (cmp g F x) ≤ (cmp g F x).card

/-- Two components sharing a vertex coincide. -/
theorem cmp_eq_of_inter {g : Gr} {F : Finset (Fin g.m)} {x y z : Fin g.v}
    (hx : z ∈ cmp g F x) (hy : z ∈ cmp g F y) : cmp g F x = cmp g F y := by
  apply cmp_eq_of_rtg
  rw [mem_cmp] at hx hy
  exact ReflTransGen.trans hx (rtg_symm hy)

theorem cmp_symm {g : Gr} {F : Finset (Fin g.m)} {x y : Fin g.v}
    (h : y ∈ cmp g F x) : x ∈ cmp g F y := by
  rw [mem_cmp] at h ⊢
  exact rtg_symm h

theorem cmp_trans {g : Gr} {F : Finset (Fin g.m)} {x y z : Fin g.v}
    (h1 : y ∈ cmp g F x) (h2 : z ∈ cmp g F y) : z ∈ cmp g F x := by
  rw [mem_cmp] at h1 h2 ⊢
  exact ReflTransGen.trans h1 h2

theorem edge_same_comp' {g : Gr} {F : Finset (Fin g.m)} {e : Fin g.m} (he : e ∈ F)
    {x : Fin g.v} (h : (g.ep e).2 ∈ cmp g F x) : (g.ep e).1 ∈ cmp g F x := by
  rw [mem_cmp] at h ⊢
  exact ReflTransGen.trans h (rtg_symm (edge_conn he))

theorem edge_cmp {g : Gr} {F : Finset (Fin g.m)} {e : Fin g.m} (he : e ∈ F)
    {u v : Fin g.v}
    (h : ((g.ep e).1 = u ∧ (g.ep e).2 = v) ∨ ((g.ep e).1 = v ∧ (g.ep e).2 = u)) :
    u ∈ cmp g F v ∨ v ∈ cmp g F u := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; rw [mem_cmp, ← h1, ← h2]; exact rtg_symm (edge_conn he)
  · right; rw [mem_cmp, ← h1, ← h2]; exact rtg_symm (edge_conn he)

/-- An `F`-edge cannot have its endpoints in two distinct `F`-components. -/
theorem edge_same_comp_iff {g : Gr} {F : Finset (Fin g.m)} {e : Fin g.m} (he : e ∈ F)
    {a b : Fin g.v} (hne : cmp g F a ≠ cmp g F b) :
    ¬ ((g.ep e).1 ∈ cmp g F a ∧ (g.ep e).2 ∈ cmp g F b) := by
  rintro ⟨h1, h2⟩
  have hE : (g.ep e).1 ∈ cmp g F b := edge_same_comp' he h2
  exact hne (cmp_eq_of_inter h1 hE)

/-- `F`-edges inside the union of two distinct components split between them. -/
theorem eIn_union_comps {g : Gr} {F : Finset (Fin g.m)} {a b : Fin g.v}
    (hne : cmp g F a ≠ cmp g F b) :
    eIn g F (cmp g F a ∪ cmp g F b) =
      eIn g F (cmp g F a) + eIn g F (cmp g F b) := by
  have hsplit : F.filter (fun e => (g.ep e).1 ∈ cmp g F a ∪ cmp g F b ∧
      (g.ep e).2 ∈ cmp g F a ∪ cmp g F b) =
    F.filter (fun e => (g.ep e).1 ∈ cmp g F a ∧ (g.ep e).2 ∈ cmp g F a) ∪
    F.filter (fun e => (g.ep e).1 ∈ cmp g F b ∧ (g.ep e).2 ∈ cmp g F b) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_union]
    refine ⟨fun ⟨he, h1, h2⟩ => ?_, ?_⟩
    · rcases h1 with h1a | h1b
      · rcases h2 with h2a | h2b
        · exact Or.inl ⟨he, h1a, h2a⟩
        · have hE1 : (g.ep e).1 ∈ cmp g F b := edge_same_comp' (x := b) he h2b
          exact absurd (cmp_eq_of_inter h1a hE1) hne
      · rcases h2 with h2a | h2b
        · have hE2 : (g.ep e).1 ∈ cmp g F a := edge_same_comp' (x := a) he h2a
          exact absurd (cmp_eq_of_inter hE2 h1b) hne
        · exact Or.inr ⟨he, h1b, h2b⟩
    · rintro (⟨he, h1, h2⟩ | ⟨he, h1, h2⟩)
      · exact ⟨he, Or.inl h1, Or.inl h2⟩
      · exact ⟨he, Or.inr h1, Or.inr h2⟩
  rw [eIn, eIn, eIn, hsplit, Finset.card_union_of_disjoint]
  refine Finset.disjoint_left.mpr fun e heA heB => ?_
  simp only [Finset.mem_filter] at heA heB
  exact hne (cmp_eq_of_inter heA.2.1 heB.2.1)

/-- Internal edge count grows by at most 1 when an edge is added. -/
theorem eIns_le (g : Gr) (F : Finset (Fin g.m)) (e : Fin g.m) (T : Finset (Fin g.v)) :
    eIn g (insert e F) T ≤ eIn g F T + 1 := by
  rw [eIn, eIn]
  have hsub : (insert e F).filter (fun x => (g.ep x).1 ∈ T ∧ (g.ep x).2 ∈ T) ⊆
      F.filter (fun x => (g.ep x).1 ∈ T ∧ (g.ep x).2 ∈ T) ∪ {e} := by
    intro x hx
    have hx' : x ∈ insert e F ∧ ((g.ep x).1 ∈ T ∧ (g.ep x).2 ∈ T) := by
      simpa [Finset.mem_filter] using hx
    rcases Finset.mem_insert.mp hx'.1 with hex | hxF
    · subst hex; exact Or.inr rfl
    · exact Or.inl ⟨hxF, hx'.2⟩
  refine (Finset.card_le_card hsub).trans ?_
  have h1 : (F.filter fun x => (g.ep x).1 ∈ T ∧ (g.ep x).2 ∈ T).card + 1 =
      (F.filter fun x => (g.ep x).1 ∈ T ∧ (g.ep x).2 ∈ T).card +
        ({e} : Finset (Fin g.m)).card := by congr 1; simp
  exact Finset.card_union_le _ _ |>.trans h1

theorem eIns_eq {g : Gr} {F : Finset (Fin g.m)} {e : Fin g.m} (heF : e ∉ F)
    {T : Finset (Fin g.v)} (hT : (g.ep e).1 ∈ T ∧ (g.ep e).2 ∈ T) :
    eIn g (insert e F) T = eIn g F T + 1 := by
  have hfil : (insert e F).filter (fun x => (g.ep x).1 ∈ T ∧ (g.ep x).2 ∈ T) =
      F.filter (fun x => (g.ep x).1 ∈ T ∧ (g.ep x).2 ∈ T) ∪ {e} := by
    ext x
    have hx' : x ∈ insert e F ∧ ((g.ep x).1 ∈ T ∧ (g.ep x).2 ∈ T) ↔
        (x ∈ F ∧ ((g.ep x).1 ∈ T ∧ (g.ep x).2 ∈ T)) ∨ x = e := by
      constructor
      · rintro ⟨h1, h2⟩
        rcases Finset.mem_insert.mp h1 with hex | hxF
        · exact Or.inr hex
        · exact Or.inl ⟨hxF, h2⟩
      · rintro (⟨h1, h2⟩ | hex)
        · exact ⟨Finset.mem_insert.mpr (Or.inr h1), h2⟩
        · subst hex
          exact ⟨Finset.mem_insert.mpr (Or.inl rfl), hT⟩
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
    exact hx'

  rw [eIn, eIn, hfil, Finset.card_union_of_disjoint]
  refine Finset.disjoint_singleton_right.mpr ?_
  intro hmem
  simp only [Finset.mem_filter] at hmem
  exact heF hmem.1

/-- Crossing-edge lemma. -/
theorem cross_exists {g : Gr} {F : Finset (Fin g.m)} {x₀ : Fin g.v}
    {W : Finset (Fin g.v)} (hW : W ⊆ cmp g F x₀) {x y : Fin g.v}
    (h : ReflTransGen (Adj g F) x y) (hxW : x ∈ W) (hyC : y ∈ cmp g F x₀) :
    y ∈ W ∨ ∃ e ∈ F, ((g.ep e).1 ∈ cmp g F x₀ ∧ (g.ep e).2 ∈ cmp g F x₀) ∧
      (((g.ep e).1 ∈ W ∧ (g.ep e).2 ∉ W) ∨ ((g.ep e).2 ∈ W ∧ (g.ep e).1 ∉ W)) := by
  induction h with
  | refl => exact Or.inl hxW
  | tail _h1 hstep ih =>
    obtain ⟨w, hw, hzy⟩ := hstep
    by_cases hcW : y ∈ W
    · exact Or.inl hcW
    · have hwc : w ∈ cmp g F x₀ := by
        have h1 : w ∈ cmp g F y ∨ y ∈ cmp g F w := edge_cmp hw hzy
        rcases h1 with h1 | h1
        · exact cmp_trans h1 hyC
        · exact cmp_trans (cmp_symm h1) hyC
      rcases ih hxW hwc with hbW | hcros
      · rcases hzy with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inr ⟨w, hw, ⟨hwc, hyC⟩, Or.inl ⟨hbW, hcW⟩⟩
        · exact Or.inr ⟨w, hw, ⟨hwc, hyC⟩, Or.inr ⟨hbW, hcW⟩⟩
      · exact Or.inr ⟨_, hcros.1, hcros.2.1, hcros.2.2⟩

end Bicir
