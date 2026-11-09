import PDTAR.SmallK33Local
namespace PDTAR
open Finset
attribute [local instance] Classical.propDecidable

/-- Every vertex of a comparison graph has degree exactly three. -/
theorem small_k33_degree {H : SimpleGraph (Fin 3 ⊕ Fin 3)}
    (hH : NoIsolated H) (he : SamePD (completeBipartiteGraph (Fin 3) (Fin 3)) H)
    (v : Fin 3 ⊕ Fin 3) : (univ.filter (H.Adj v)).card = 3 := by
  classical
  let N := univ.filter (H.Adj v)
  have hlo : 3 ≤ N.card := by
    obtain ⟨a,b,c,hab,hac,hbc,hva,hvb,hvc⟩ := small_k33_three_neighbors hH he v
    have hs : ({a,b,c} : Finset (Fin 3 ⊕ Fin 3)) ⊆ N := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp [N,hva,hvb,hvc]
    have hc : ({a,b,c} : Finset (Fin 3 ⊕ Fin 3)).card = 3 := by simp [hab,hac,hbc]
    have hh := card_le_card hs
    omega
  have hhi : N.card ≤ 3 := by
    by_contra! hn
    have hvN : v ∉ N := by simp [N]
    have hc : (insert v N).card = N.card + 1 := card_insert_of_notMem hvN
    have hsub : insert v N ⊆ closed H {v} := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact subset_closed H _ (by simp)
      · exact (mem_closed H _ _).mpr (.inr ⟨v,by simp,(mem_filter.mp hx).2⟩)
    have hbound := card_le_card hsub
    have hsize : (univ : Finset (Fin 3 ⊕ Fin 3)).card = 6 := by simp
    have hdiff := card_sdiff_of_subset (subset_univ (closed H {v}))
    have hone : (univ \ closed H {v}).card ≤ 1 := by omega
    have hp : IsPD H {v} := ⟨2,small_step_of_one_missing hH (by
      intro x y hx hy
      change x ∉ closed H {v} at hx
      change y ∉ closed H {v} at hy
      exact card_le_one.mp hone x (by simp [hx]) y (by simp [hy]))⟩
    exact small_k33_singleton v ((he _).mpr hp)
  change N.card = 3
  omega
#print axioms small_k33_degree
end PDTAR
