import PDTAR.SmallStarRigidity
namespace PDTAR
open Finset

theorem starRigidityRemaining : StarRigidityRemaining := by
  intro t ht
  constructor
  · intro H hH he
    have hk : CompleteBetween (completeBipartiteGraph (Fin 1) (Fin t))
        (rightPart 1 t) {Sum.inl 0} := by
      have hh := completeBetween_swap (sum_parts 1 t)
      have hleft : leftPart 1 t = {Sum.inl 0} := by
        ext x; cases x with
        | inl a => fin_cases a; simp [leftPart]
        | inr b => simp [leftPart]
      simpa [hleft] using hh
    have h := small_star_rigid hk he (by simpa [rightPart] using ht) hH
    subst H
    exact ⟨SimpleGraph.Iso.refl⟩
  · intro H hH he
    have hk : CompleteBetween (completeBipartiteGraph (Fin t) (Fin 1))
        (leftPart t 1) {Sum.inr 0} := by
      have hh := sum_parts t 1
      have hright : rightPart t 1 = {Sum.inr 0} := by
        ext x; cases x with
        | inl a => simp [rightPart]
        | inr b => fin_cases b; simp [rightPart]
      simpa [hright] using hh
    have h := small_star_rigid hk he (by simpa [leftPart] using ht) hH
    subst H
    exact ⟨SimpleGraph.Iso.refl⟩
#print axioms starRigidityRemaining
end PDTAR
