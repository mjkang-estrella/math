import PDTAR.SmallEdge
namespace PDTAR

/-- OPEN: labelled PD-family rigidity for stars, in both orientations.
No TAR or reduction assertion is included in this obligation. -/
def StarRigidityRemaining : Prop := ∀ t : ℕ, 3 ≤ t →
  (∀ H : SimpleGraph (Fin 1 ⊕ Fin t), NoIsolated H →
    SamePD (completeBipartiteGraph (Fin 1) (Fin t)) H →
    Nonempty (H ≃g completeBipartiteGraph (Fin 1) (Fin t))) ∧
  (∀ H : SimpleGraph (Fin t ⊕ Fin 1), NoIsolated H →
    SamePD (completeBipartiteGraph (Fin t) (Fin 1)) H →
    Nonempty (H ≃g completeBipartiteGraph (Fin t) (Fin 1)))

/-- OPEN: labelled six-vertex PD-family rigidity; no enumeration of all graphs. -/
def ThreeThreeRigidityRemaining : Prop :=
  ∀ H : SimpleGraph (Fin 3 ⊕ Fin 3), NoIsolated H →
    SamePD (completeBipartiteGraph (Fin 3) (Fin 3)) H →
    Nonempty (H ≃g completeBipartiteGraph (Fin 3) (Fin 3))

/-- OPEN: construct the specified added-edge witnesses, including P3 versus K3
at (1,2) and (2,1). This states the exact residual labelled witness property.
It requires neither a TAR isomorphism nor any reduction hypothesis. -/
def TwoWitnessRemaining : Prop := ∀ s t : ℕ, 1 ≤ s → 1 ≤ t → (s = 2 ∨ t = 2) →
  ∃ H : SimpleGraph (Fin s ⊕ Fin t), NoIsolated H ∧
    SamePD (completeBipartiteGraph (Fin s) (Fin t)) H ∧
    ¬ Nonempty (H ≃g completeBipartiteGraph (Fin s) (Fin t))

/-- General sum-type no-isolation bridge; it includes both orientations. -/
theorem small_sum_noIsolated (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    NoIsolated (completeBipartiteGraph (Fin s) (Fin t)) := by
  intro x
  cases x with
  | inl a => exact ⟨Sum.inr ⟨0,by omega⟩,by simp [completeBipartiteGraph]⟩
  | inr b => exact ⟨Sum.inl ⟨0,by omega⟩,by simp [completeBipartiteGraph]⟩

theorem stars_of_rigidity (hR : ReductionRemaining) (hS : StarRigidityRemaining) :
    StarsRemaining := by
  intro t ht
  obtain ⟨hleft,hright⟩ := hS t ht
  constructor
  · intro W _ _ H hH hiso
    obtain ⟨H',⟨e⟩,he⟩ := hR _ _ _ H (small_sum_noIsolated 1 t (by omega) (by omega)) hH hiso
    obtain ⟨f⟩ := hleft H' (noIsolated_iso hH e) he
    exact ⟨e.trans f⟩
  · intro W _ _ H hH hiso
    obtain ⟨H',⟨e⟩,he⟩ := hR _ _ _ H (small_sum_noIsolated t 1 (by omega) (by omega)) hH hiso
    obtain ⟨f⟩ := hright H' (noIsolated_iso hH e) he
    exact ⟨e.trans f⟩

theorem threeThree_of_rigidity (hR : ReductionRemaining) (hT : ThreeThreeRigidityRemaining) :
    ThreeThreeRemaining := by
  intro W _ _ H hH hiso
  obtain ⟨H',⟨e⟩,he⟩ := hR _ _ _ H (small_sum_noIsolated 3 3 (by omega) (by omega)) hH hiso
  obtain ⟨f⟩ := hT H' (noIsolated_iso hH e) he
  exact ⟨e.trans f⟩

theorem two_of_witness (hT : TwoWitnessRemaining) : TwoRemaining := by
  intro s t hs ht htwo hu
  obtain ⟨H,hH,he,hn⟩ := hT s t hs ht htwo
  exact hn (hu _ H hH ⟨(samePD_tar_iso he).symm⟩)
end PDTAR
