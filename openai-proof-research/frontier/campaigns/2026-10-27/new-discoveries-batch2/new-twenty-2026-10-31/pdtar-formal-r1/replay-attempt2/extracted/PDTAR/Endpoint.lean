import PDTAR.Remaining
namespace PDTAR
open Finset

def leftPart (s t : ℕ) : Finset (Fin s ⊕ Fin t) :=
  univ.map ⟨Sum.inl, Sum.inl_injective⟩
def rightPart (s t : ℕ) : Finset (Fin s ⊕ Fin t) :=
  univ.map ⟨Sum.inr, Sum.inr_injective⟩

theorem sum_parts (s t : ℕ) :
    CompleteBetween (completeBipartiteGraph (Fin s) (Fin t)) (leftPart s t) (rightPart s t) := by
  constructor
  · constructor
    · apply disjoint_left.mpr
      intro x
      cases x <;> simp [leftPart,rightPart]
    · ext x
      cases x <;> simp [leftPart,rightPart]
  · intro x y
    cases x <;> cases y <;> simp [completeBipartiteGraph,leftPart,rightPart]

theorem sum_noIsolated (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    NoIsolated (completeBipartiteGraph (Fin s) (Fin t)) := by
  intro x
  cases x with
  | inl a => exact ⟨Sum.inr ⟨0,by omega⟩,by simp [completeBipartiteGraph]⟩
  | inr b => exact ⟨Sum.inl ⟨0,by omega⟩,by simp [completeBipartiteGraph]⟩

/-- CONDITIONAL only: all six named Props are unproved obligations. -/
theorem mathdb_353203_conditional
    (reduction : ReductionRemaining) (core : CoreRemaining)
    (edge : EdgeRemaining) (stars : StarsRemaining)
    (threeThree : ThreeThreeRemaining) (two : TwoRemaining)
    (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    TARUnique (completeBipartiteGraph (Fin s) (Fin t)) ↔ (s ≠ 2 ∧ t ≠ 2) := by
  constructor
  · intro hu
    constructor
    · intro he; exact two s t hs ht (.inl he) hu
    · intro he; exact two s t hs ht (.inr he) hu
  · rintro ⟨hs2,ht2⟩
    by_cases hs1 : s = 1
    · subst s
      by_cases ht1 : t = 1
      · subst t; exact edge
      · exact (stars t (by omega)).1
    by_cases ht1 : t = 1
    · subst t; exact (stars s (by omega)).2
    by_cases h33 : s = 3 ∧ t = 3
    · obtain ⟨rfl,rfl⟩ := h33; exact threeThree
    have hs3 : 3 ≤ s := by omega
    have ht3 : 3 ≤ t := by omega
    intro W _ _ H hH hiso
    obtain ⟨H',⟨e⟩,hpd⟩ := reduction _ _ _ H (sum_noIsolated s t hs ht) hH hiso
    have hcore := core _ _ H' (leftPart s t) (rightPart s t) (sum_parts s t)
      (by simpa [leftPart] using hs3) (by simpa [rightPart] using ht3)
      (by simpa [leftPart,rightPart] using (not_and_or.mp h33)) hpd
    subst H'
    exact ⟨e⟩
end PDTAR
