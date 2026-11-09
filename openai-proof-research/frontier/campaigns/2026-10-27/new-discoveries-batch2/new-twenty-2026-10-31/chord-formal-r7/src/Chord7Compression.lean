import ChordModel4Erasure
namespace Chord.Round7
open Equiv Model3 Model4

attribute [local instance] Classical.propDecidable
/-- A local contraction certificate needs no backward orbit argument. At retained
points its retraction advances by the small permutation; elsewhere it stays put. -/
theorem orbitCount_contraction {α β : Type*} [Fintype α] [Fintype β]
    (f : Perm α) (g : Perm β) (e : α → β) (r : β → α)
    (hretract : ∀ x, r (e x) = x)
    (hstep : ∀ y, r (g y) = if h : ∃ x, e x = y then f h.choose else r y)
    (hmeet : ∀ y, Perm.SameCycle g (e (r y)) y) :
    orbitCount f = orbitCount g := by
  classical
  have hinj : Function.Injective e := Function.LeftInverse.injective hretract
  have hs (x : α) : r (g (e x)) = f x := by
    have hx : ∃ z, e z = e x := ⟨x, rfl⟩
    rw [hstep, dite_eq_left hx, hinj hx.choose_spec]
  apply orbitCount_of_retraction f g e r hretract
  · intro x
    have hh := hmeet (g (e x))
    rw [hs] at hh
    exact (Perm.SameCycle.refl g (e x)).apply_right.trans hh.symm
  · intro y
    rw [hstep]
    split
    · rename_i h
      have hr : r y = h.choose := (congrArg r h.choose_spec).symm.trans (hretract _)
      rw [hr]
      exact (Perm.SameCycle.refl f _).apply_right
    · exact Perm.SameCycle.refl _ _
  · exact hmeet

/-- A decreasing rank certifies that every collapsed point reaches its retained
representative. This rules out hidden cycles entirely inside the erased set. -/
theorem sameCycle_of_rank {α β : Type*} [Fintype β]
    (g : Perm β) (e : α → β) (r : β → α) (rank : β → Nat)
    (hdesc : ∀ y, y ≠ e (r y) → r (g y) = r y ∧ rank (g y) < rank y) :
    ∀ y, Perm.SameCycle g (e (r y)) y := by
  intro y
  have aux : ∀ k y, rank y = k → Perm.SameCycle g (e (r y)) y := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro y hy
      by_cases he : y = e (r y)
      · rw [← he]
      · have hd := hdesc y he
        have hh := ih (rank (g y)) (by omega) (g y) rfl
        rw [hd.1] at hh
        exact hh.trans (Perm.SameCycle.refl g y).apply_right.symm
  exact aux (rank y) y rfl

/-- A finite, local certificate for compression. It suffices to check the
retained transitions and a strictly decreasing rank on all omitted points. -/
theorem orbitCount_of_rank {α β : Type*} [Fintype α] [Fintype β]
    (f : Perm α) (g : Perm β) (e : α → β) (r : β → α) (rank : β → Nat)
    (hretract : ∀ x, r (e x) = x)
    (hretained : ∀ x, r (g (e x)) = f x)
    (hdesc : ∀ y, y ≠ e (r y) → r (g y) = r y ∧ rank (g y) < rank y) :
    orbitCount f = orbitCount g := by
  have hm := sameCycle_of_rank g e r rank hdesc
  apply orbitCount_of_retraction f g e r hretract
  · intro x
    have hh := hm (g (e x))
    rw [hretained] at hh
    exact (Perm.SameCycle.refl g (e x)).apply_right.trans hh.symm
  · intro y
    by_cases he : y = e (r y)
    · have hh := hretained (r y)
      rw [← he] at hh
      rw [hh]
      exact (Perm.SameCycle.refl f _).apply_right
    · rw [(hdesc y he).1]
  · exact hm


/-- The same certificate also preserves and reflects connectivity of retained
points, supplying the face-sensitive part needed by EndEdgeSurgery. -/
theorem sameCycle_iff_of_rank {α β : Type*} [Fintype α] [Fintype β]
    (f : Perm α) (g : Perm β) (e : α → β) (r : β → α) (rank : β → Nat)
    (hretract : ∀ x, r (e x) = x)
    (hretained : ∀ x, r (g (e x)) = f x)
    (hdesc : ∀ y, y ≠ e (r y) → r (g y) = r y ∧ rank (g y) < rank y)
    (x y : α) : Perm.SameCycle f x y ↔ Perm.SameCycle g (e x) (e y) := by
  have hm := sameCycle_of_rank g e r rank hdesc
  have he (x : α) : Perm.SameCycle g (e x) (e (f x)) := by
    have hh := hm (g (e x))
    rw [hretained] at hh
    exact (Perm.SameCycle.refl g (e x)).apply_right.trans hh.symm
  have hr (z : β) : Perm.SameCycle f (r z) (r (g z)) := by
    by_cases hz : z = e (r z)
    · have hh := hretained (r z)
      rw [← hz] at hh
      rw [hh]
      exact (Perm.SameCycle.refl f _).apply_right
    · rw [(hdesc z hz).1]
  constructor
  · exact sameCycle_map f g e he
  · intro h
    simpa only [hretract] using sameCycle_map g f r hr h

#print axioms orbitCount_contraction
#print axioms sameCycle_of_rank
#print axioms orbitCount_of_rank
#print axioms sameCycle_iff_of_rank
end Chord.Round7
