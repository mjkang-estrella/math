import Structure
namespace Percolation
set_option autoImplicit false
structure Collineation5 where
  p : Points 5 → Points 5
  pinv : Points 5 → Points 5
  l : Points 5 → Points 5
  linv : Points 5 → Points 5
  pp : ∀ x, p (pinv x) = x
  pi : ∀ x, pinv (p x) = x
  ll : ∀ x, l (linv x) = x
  li : ∀ x, linv (l x) = x
  perm : ((List.finRange 31).map p).Perm (List.finRange 31)
  incidence_preserved : ∀ x y, incidence (p x) (l y) = incidence x y

def transport5 (e : Collineation5) (a : Infection 5) : Infection 5 := a ∘ e.p

theorem card_map5 (e : Collineation5) (f : Points 5 → Bool) :
    card (List.finRange 31) (f ∘ e.p) = card (List.finRange 31) f := by
  have h := (e.perm.filter f).length_eq
  simpa [card, List.filter_map, Function.comp_def] using h

theorem count_transport5 (e : Collineation5) (a : Infection 5) (l : Points 5) :
    countOn PG5 (transport5 e a) l = countOn PG5 a (e.l l) := by
  unfold countOn
  rw [← card_map5 e (fun p => a p && PG5.inc p (e.l l))]
  congr 1
  funext p
  simp only [Function.comp_apply, transport5, PG5, e.incidence_preserved]

theorem step_transport5 (e : Collineation5) (r : Nat) (a : Infection 5) :
    step PG5 r (transport5 e a) = transport5 e (step PG5 r a) := by
  funext p
  apply Bool.eq_iff_iff.mpr
  change step PG5 r (transport5 e a) p = true ↔ step PG5 r a (e.p p) = true
  simp only [step, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨l, _, hi, hc⟩)
    · exact Or.inl h
    · right
      exact ⟨e.l l, by simp, (e.incidence_preserved p l).trans hi,
        by simpa only [← count_transport5 e a l] using hc⟩
  · rintro (h | ⟨l, _, hi, hc⟩)
    · exact Or.inl h
    · right
      refine ⟨e.linv l, by simp, ?_, ?_⟩
      · have h := e.incidence_preserved p (e.linv l)
        rw [e.ll] at h
        exact h.symm.trans hi
      · rw [count_transport5, e.ll]
        exact hc

theorem rounds_transport5 (e : Collineation5) (r : Nat) (a : Infection 5) (n : Nat) :
    rounds PG5 r (transport5 e a) n = transport5 e (rounds PG5 r a n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step PG5 r (rounds PG5 r (transport5 e a) n) = _
    rw [ih, step_transport5]
    rfl

theorem full_transport5 (e : Collineation5) (a : Infection 5) :
    Full (transport5 e a) ↔ Full a := by
  constructor
  · intro h p
    have h' := h (e.pinv p)
    simpa only [transport5, Function.comp_apply, e.pp] using h'
  · intro h p
    exact h (e.p p)

theorem percolates_transport5 (e : Collineation5) (r : Nat) (a : Infection 5) :
    Percolates PG5 r (transport5 e a) ↔ Percolates PG5 r a := by
  simp only [Percolates, rounds_transport5, full_transport5]

theorem timeIs_transport5 (e : Collineation5) (r : Nat) (a : Infection 5) (t : Nat) :
    TimeIs PG5 r (transport5 e a) t ↔ TimeIs PG5 r a t := by
  simp only [TimeIs, rounds_transport5, full_transport5]

theorem minimal_transport5 (e : Collineation5) (r : Nat) (a : Infection 5)
    (h : Minimal PG5 r a) : Minimal PG5 r (transport5 e a) := by
  refine ⟨(percolates_transport5 e r a).mpr h.1, ?_⟩
  intro b hb hne hp
  let c : Infection 5 := b ∘ e.pinv
  have hc : Subset c a := by
    intro p hp
    have hh := hb (e.pinv p) hp
    simpa only [transport5, Function.comp_apply, e.pp] using hh
  have he : transport5 e c = b := by
    funext p
    simp only [transport5, c, Function.comp_apply, e.pi]
  apply h.2 c hc
  · intro hca
    apply hne
    rw [← he, hca]
  · apply (percolates_transport5 e r c).mp
    rw [he]
    exact hp
end Percolation
