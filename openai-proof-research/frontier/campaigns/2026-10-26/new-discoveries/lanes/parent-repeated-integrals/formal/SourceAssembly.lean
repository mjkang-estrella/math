import MomentRepresentation
import SmoothWitness

open Set

namespace RepeatedIntegrals

noncomputable section

theorem sourceW_eq_smoothMomentImage (n : ℕ)
    (hc : Convex ℝ (smoothMomentSet n)) (ho : IsOpen (smoothMomentSet n)) :
    SourceW n = endpointMomentTransform n '' smoothMomentSet n := by
  apply Set.Subset.antisymm
  · intro b hb
    obtain ⟨d⟩ := source_measure_exists hb
    have := d.finite
    have := d.atomless
    exact ⟨measureMoments n d.measure,
      atomless_measure_mem_smoothMomentSet hc ho d.supported d.mass_pos,
      sourceMeasure_transform d⟩
  · exact smoothMomentImage_subset_sourceW n

theorem source_conjecture_of_moment_openness
    (hc : ∀ n, Convex ℝ (smoothMomentSet n))
    (ho : ∀ n, IsOpen (smoothMomentSet n)) : SourceConjecture371768 := by
  intro n
  have he := sourceW_eq_smoothMomentImage n (hc n) (ho n)
  constructor
  · rw [he]
    exact (endpointMomentTransform n).toHomeomorph.isOpenMap _ (ho n)
  · intro b hb
    rw [he] at hb
    obtain ⟨y, ⟨ρ, hρ, hρy⟩, hyb⟩ := hb
    refine ⟨repeatedPrimitive (n + 1) ρ, ?_⟩
    rw [← hyb, ← hρy]
    exact repeatedPrimitive_goodWitness n hρ

end

end RepeatedIntegrals
