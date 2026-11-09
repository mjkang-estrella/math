import PDTAR.SmallTwoWitness
import PDTAR.ReductionProof
namespace PDTAR
set_option linter.unusedSectionVars false
open Finset
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
attribute [local instance] Classical.propDecidable

theorem mem_step_literal (O : Finset V) (u : V) :
    u ∈ step G O ↔ u ∈ O ∨ ∃ v ∈ O,
      (Finset.univ.filter fun w => G.Adj v w ∧ w ∉ O) = {u} := by
  classical
  rw [mem_step]
  constructor
  · rintro (h | ⟨v,hv,ha,huniq⟩)
    · exact .inl h
    · by_cases ho : u ∈ O
      · exact .inl ho
      · right
        refine ⟨v,hv,?_⟩
        ext w
        simp only [mem_filter,mem_univ,true_and,mem_singleton]
        constructor
        · rintro ⟨hw,hwo⟩; exact huniq w hw hwo
        · rintro rfl; exact ⟨ha,ho⟩
  · rintro (h | ⟨v,hv,he⟩)
    · exact .inl h
    · have hu : u ∈ (univ.filter fun w => G.Adj v w ∧ w ∉ O) := he ▸ (by simp)
      have ha := (mem_filter.mp hu).2.1
      right
      refine ⟨v,hv,ha,?_⟩
      intro w hw hwo
      have hh : w ∈ (univ.filter fun w => G.Adj v w ∧ w ∉ O) := by simp [hw,hwo]
      rw [he] at hh
      exact mem_singleton.mp hh

theorem isFort_card_literal (F : Finset V) : IsFort G F ↔ F.Nonempty ∧
    ∀ v, v ∉ F → (F.filter (G.Adj v)).card ≠ 1 := by
  classical
  constructor
  · rintro ⟨hne,h⟩
    refine ⟨hne,?_⟩
    intro v hv hc
    obtain ⟨u,hu⟩ := card_eq_one.mp hc
    have hum : u ∈ F.filter (G.Adj v) := hu ▸ (by simp)
    obtain ⟨w,hw,hne,ha⟩ := h v hv u (mem_filter.mp hum).1 (mem_filter.mp hum).2
    have hwm : w ∈ F.filter (G.Adj v) := mem_filter.mpr ⟨hw,ha⟩
    rw [hu] at hwm
    exact hne (mem_singleton.mp hwm)
  · rintro ⟨hne,h⟩
    refine ⟨hne,?_⟩
    intro v hv u hu ha
    by_contra! hn
    apply h v hv
    have he : F.filter (G.Adj v) = {u} := by
      ext w
      simp only [mem_filter,mem_singleton]
      constructor
      · rintro ⟨hw,hadj⟩
        by_contra hh
        exact hn w hw hh hadj
      · rintro rfl; exact ⟨hu,ha⟩
    simp [he]

theorem empty_not_isPD [Nonempty V] : ¬ IsPD G ∅ := by
  classical
  intro hp
  have hf : IsFort G (univ : Finset V) := ⟨univ_nonempty,by simp⟩
  have hh := (fort_duality G ∅).mp hp univ hf
  simp [closed] at hh
/-- The reduction also rules out an empty comparison vertex type. -/
theorem small_empty_comparison (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (W : Type) [Fintype W] [DecidableEq W] [IsEmpty W] (H : SimpleGraph W)
    (hH : NoIsolated H) :
    ¬ Nonempty (tar H ≃g tar (completeBipartiteGraph (Fin s) (Fin t))) := by
  intro hi
  obtain ⟨H',⟨e⟩,_⟩ := reductionRemaining _ _ _ H (sum_noIsolated s t hs ht) hH hi
  exact isEmptyElim (e.symm (Sum.inl ⟨0,by omega⟩))
end PDTAR
