import PDTAR.FinalComplete
namespace FidelityReviewer
open PDTAR Finset
open scoped symmDiff
abbrev K23 := completeBipartiteGraph (Fin 2) (Fin 3)
abbrev K34 := completeBipartiteGraph (Fin 3) (Fin 4)
-- Direct literal round calculation, independent of the family classification.
theorem left23 : IsPD K23 {Sum.inl 0} := by
  refine ⟨2, ?_⟩
  apply eq_univ_of_forall
  intro x
  rcases x with a | b
  · fin_cases a <;> simp [obs, propagate, step, closed, completeBipartiteGraph]
  · simp [obs, propagate, step, closed, completeBipartiteGraph]
-- A missing pair on one side is a fort disjoint from the observed neighbourhood.
theorem right23 : ¬ IsPD K23 {Sum.inr 0} := by
  intro hp
  have hf : IsFort K23 {Sum.inr 1, Sum.inr 2} := by
    refine ⟨by simp, ?_⟩
    intro v hv u hu ha
    rcases v with a | b
    · rcases mem_insert.mp hu with rfl | hu
      · exact ⟨Sum.inr 2, by simp, by decide, by simp [completeBipartiteGraph]⟩
      · have he := mem_singleton.mp hu
        subst u
        exact ⟨Sum.inr 1, by simp, by decide, by simp [completeBipartiteGraph]⟩
    · rcases mem_insert.mp hu with rfl | hu
      · simp [completeBipartiteGraph] at ha
      · have he := mem_singleton.mp hu
        subst u; simp [completeBipartiteGraph] at ha
  obtain ⟨u,hu⟩ := (fort_duality K23 _).mp hp _ hf
  rcases mem_insert.mp (mem_inter.mp hu).1 with rfl | hu'
  · simpa [closed, completeBipartiteGraph] using (mem_inter.mp hu).2
  · have he := mem_singleton.mp hu'
    subst u
    simpa [closed, completeBipartiteGraph] using (mem_inter.mp hu).2

theorem mixed34 : IsPD K34 {Sum.inl 0, Sum.inr 0} := by
  refine ⟨1, ?_⟩
  ext x
  rcases x with a | b <;> simp [obs, propagate, closed, completeBipartiteGraph]

theorem two_left34 : IsPD K34 {Sum.inl 0, Sum.inl 1} := by
  refine ⟨2, ?_⟩
  apply eq_univ_of_forall
  intro x
  rcases x with a | b
  · fin_cases a <;> simp [obs, propagate, step, closed, completeBipartiteGraph]
    all_goals omega
  · simp [obs, propagate, step, closed, completeBipartiteGraph]


theorem one_left34 : ¬ IsPD K34 {Sum.inl 0} := by
  have hn := erase_pair_not_isPD (sum_parts 3 4)
    (x := Sum.inl 1) (y := Sum.inl 2)
    (by simp [leftPart]) (by simp [leftPart]) (by decide)
  have he : leftPart 3 4 \ {Sum.inl 1, Sum.inl 2} = {Sum.inl 0} := by
    ext x
    rcases x with a | b
    · fin_cases a <;> simp [leftPart]
    · simp [leftPart]
  simpa only [he] using hn

-- Prove the empty-set case directly by induction on the rounds.
theorem empty_bad {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) : ¬ IsPD G ∅ := by
  classical
  have hc : closed G ∅ = ∅ := by ext x; simp [closed]
  have hs : step G ∅ = ∅ := by ext x; simp [step]
  have hp : ∀ n, propagate G ∅ n = ∅ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [propagate, ih, hs]
  rintro ⟨n,hn⟩
  have ho : obs G ∅ n = ∅ := by
    cases n with
    | zero => rfl
    | succ n => simp [obs, hc, hp]
  rw [ho] at hn
  have h := congrArg (fun S => Classical.choice (inferInstance : Nonempty V) ∈ S) hn
  simp at h

theorem adjacent23 : (tar K23).Adj
    ⟨{Sum.inl 0}, left23⟩
    ⟨{Sum.inl 0, Sum.inr 0}, mixed_pair_isPD (sum_parts 2 3)
      (by simp [leftPart]) (by simp [rightPart])⟩ := by
  change (({Sum.inl 0} : Finset (Fin 2 ⊕ Fin 3)) ∆ {Sum.inl 0, Sum.inr 0}).card = 1
  decide
#print axioms PDTAR.mathdb_353203
#print axioms PDTAR.coreRemaining
#print axioms PDTAR.reductionRemaining
end FidelityReviewer
