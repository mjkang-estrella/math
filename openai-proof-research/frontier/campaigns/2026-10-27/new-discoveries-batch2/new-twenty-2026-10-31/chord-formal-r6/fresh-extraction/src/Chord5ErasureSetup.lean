import ChordModel4Normalization
import ChordComb4Planarity
namespace Chord.Round5
open Equiv Model3

/-- A single-chord subdiagram omits exactly one paired pair of endpoints. -/
theorem omitted_pair {n} {D : Diagram (n+1)} {A : Diagram n}
    (S : Subdiagram A D) :
    ∃ p, (∀ i, S.positions i ≠ p) ∧
      ∀ x, (∃ i, S.positions i = x) ↔ x ≠ p ∧ x ≠ D.partner p := by
  classical
  have hnot : ¬Function.Surjective S.positions := by
    intro h
    have hh := Fintype.card_le_of_surjective _ h
    simp only [Fintype.card_fin] at hh
    omega
  obtain ⟨p,hp⟩ : ∃ p, ∀ i, S.positions i ≠ p := by
    simpa only [Function.Surjective, not_forall, not_exists] using hnot
  have hq : ∀ i, S.positions i ≠ D.partner p := by
    intro i hi
    have hh := S.closed i
    rw [hi, D.involutive] at hh
    exact hp _ hh.symm
  let im := Finset.univ.image S.positions
  have hic : im.card = 2*n := by
    rw [Finset.card_image_of_injective _ S.increasing.injective]
    simp
  have hsub : im ⊆ Comb4.keptAfter D p := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    simp [Comb4.keptAfter, hp i, hq i]
  have heq : im = Comb4.keptAfter D p :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hic, Comb4.keptAfter_card])
  refine ⟨p,hp,?_⟩
  intro x
  have hm : (∃ i, S.positions i = x) ↔ x ∈ im := by simp [im]
  rw [hm,heq]
  simp [Comb4.keptAfter]

/-- The C-successor swap is independent of which omitted endpoint is chosen. -/
theorem omitted_swap_eq {n} {D : Diagram (n+1)} {A : Diagram n}
    (S : Subdiagram A D) (p q : Fin (2*(n+1)))
    (hp : ∀ i, S.positions i ≠ p) (hq : ∀ i, S.positions i ≠ q) :
    swap (chordDart p) (chordDart (D.partner p)) =
      swap (chordDart q) (chordDart (D.partner q)) := by
  classical
  obtain ⟨r,_,hr⟩ := omitted_pair S
  have hv : ∀ x, (∀ i, S.positions i ≠ x) → x = r ∨ x = D.partner r := by
    intro x hx
    by_contra h
    have hh : x ≠ r ∧ x ≠ D.partner r := not_or.mp h
    obtain ⟨i,hi⟩ := (hr x).mpr hh
    exact hx i hi
  rcases hv p hp with rfl | rfl <;> rcases hv q hq with rfl | rfl
  · rfl
  · rw [D.involutive, swap_comm]
  · rw [D.involutive, swap_comm]
  · rfl

/-- The existential in BandErasure can equivalently be proved at every omitted endpoint. -/
theorem bandErasure_iff_every : BandErasure ↔
    ∀ n (D : Diagram (n+1)) (A : Diagram n) (S : Subdiagram A D)
      (c : Sides (n+1)) p, (∀ i, S.positions i ≠ p) →
      Model3.orbitCount (Model2.faceEquiv D c *
        swap (chordDart p) (chordDart (D.partner p))) = boundary A (restrictSides S c) := by
  constructor
  · intro h n D A S c p hp
    obtain ⟨q,hq,h⟩ := h n D A S c
    rw [omitted_swap_eq S p q hp hq]
    exact h
  · intro h n D A S c
    obtain ⟨p,hp,_⟩ := omitted_pair S
    exact ⟨p,hp,h n D A S c p hp⟩
end Chord.Round5
