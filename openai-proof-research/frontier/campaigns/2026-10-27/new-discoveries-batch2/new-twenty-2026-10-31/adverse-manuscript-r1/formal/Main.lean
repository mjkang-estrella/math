import Bridges
import Quadratic

open scoped BigOperators
namespace Adverse381433

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem incidence_columnQ : ∀ p : Cell, ∑ l : Line, incidenceQ l p = 3 := by
  decide +kernel

theorem incidence_columnR (p : Cell) : ∑ l : Line, incidenceR l p = 3 := by
  unfold incidenceR
  exact_mod_cast incidence_columnQ p

theorem fractional_sumR (v : Cell) (l : Line) :
    ∑ p : Cell, incidenceR l p * (fractionalAt v p : ℝ) = 1 := by
  unfold incidenceR
  exact_mod_cast (all_certificates v).2.2.1 l

theorem fractional_nonnegR (v p : Cell) : 0 ≤ (fractionalAt v p : ℝ) := by
  exact_mod_cast (all_certificates v).1 p

theorem global_upsilon : upsilon latinGraph = 6 := by
  exact upsilon_eq_six latinGraph incidenceR incidence_identityR global_least
    incidence_columnR (fun p => (fractionalAt (0,0) p : ℝ))
    (fractional_nonnegR (0,0)) (fractional_sumR (0,0))

theorem deletion_fractional_sum (v : Cell) (l : Line) :
    (∑ p : deletionVertices latinGraph v, incidenceR l p.val * (fractionalAt v p.val : ℝ)) = 1 := by
  classical
  rw [← fractional_sumR v l]
  symm
  apply Finset.sum_congr_set {p | ¬latinGraph.Adj v p}
  · intro p hp
    rfl
  · intro p hp
    have ha : latinGraph.Adj v p := Classical.not_not.mp hp
    rw [(all_certificates v).2.1 p ha |>.1]
    simp

theorem deletion_upsilon (v : Cell) : upsilon (deleteOpen latinGraph v) = 6 := by
  classical
  exact upsilon_eq_six (deleteOpen latinGraph v) (fun l p => incidenceR l p.val)
    (deletion_gram v) (deletion_least v) (fun p => incidence_columnR p.val)
    (fun p => (fractionalAt v p.val : ℝ))
    (fun p => fractional_nonnegR v p.val) (deletion_fractional_sum v)

theorem no_isolated_vertices : ∀ v : Cell, ∃ w, latinGraph.Adj v w := by
  unfold latinGraph
  decide +kernel

theorem graph_adverse : Adverse latinGraph := by
  refine ⟨no_isolated_vertices, ⟨6, ?_⟩, ⟨-3, ?_⟩, ?_⟩
  · simpa using global_upsilon
  · simpa using global_least
  · intro v
    exact ⟨(deletion_upsilon v).trans global_upsilon.symm,
      (deletion_least v).trans global_least.symm⟩

theorem graph_not_Q : ¬QGraph latinGraph := by
  unfold QGraph
  rw [alpha_eq_five, global_upsilon]
  norm_num

theorem refutation : ¬CardosoLuzConjecture := by
  intro h
  exact graph_not_Q (h Cell latinGraph graph_adverse)

noncomputable def SourceConjecture : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    (∃ a b, G.Adj a b) → Adverse G → QGraph G

theorem refutation_of_source_statement : ¬SourceConjecture := by
  intro h
  exact graph_not_Q (h Cell latinGraph ⟨(0,0),(0,1), by unfold latinGraph; decide⟩ graph_adverse)

end Adverse381433
