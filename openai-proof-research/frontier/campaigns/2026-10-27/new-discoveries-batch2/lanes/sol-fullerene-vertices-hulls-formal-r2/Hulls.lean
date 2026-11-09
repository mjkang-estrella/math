import Literal
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace FullereneGeometry
theorem hull_of_complete_vertices {n : ℕ} (q : Fin n → E)
    (hc : IsCompact (poly q)) {m : ℕ} (p : Fin m → E)
    (hv : (poly q).extremePoints ℝ = Set.range p) :
    poly q = convexHull ℝ (Set.range p) := by
  have h := closure_convexHull_extremePoints hc (poly_convex q)
  rw [hv, ((Set.finite_range p).isClosed_convexHull ℝ).closure_eq] at h
  exact h.symm

theorem section_hull_of_complete_vertices {n : ℕ} (q : Fin n → E)
    (hc : IsCompact (poly q)) {m : ℕ} (p : Fin m → E)
    (hv : (poly q).extremePoints ℝ = Set.range p) (i : Fin n) :
    facetSection q i = convexHull ℝ {x ∈ Set.range p | dot (q i) x = 1} := by
  have hs : IsClosed (facetSection q i) :=
    (poly_closed q).inter (isClosed_eq (dot_continuous (q i)) continuous_const)
  have hcomp : IsCompact (facetSection q i) := hc.of_isClosed_subset hs (fun _ h => h.1)
  have hconv : Convex ℝ (facetSection q i) := by
    intro x hx y hy a b ha hb hab
    refine ⟨poly_convex q hx.1 hy.1 ha hb hab, ?_⟩
    change (normal (q i)) (a • x + b • y) = 1
    rw [map_add, map_smul, map_smul]
    change a * dot (q i) x + b * dot (q i) y = 1
    rw [hx.2, hy.2]; linarith
  have he : (facetSection q i).extremePoints ℝ = {x ∈ Set.range p | dot (q i) x = 1} := by
    ext x
    constructor
    · intro hx
      exact ⟨hv ▸ (facetSection_extreme q i).extremePoints_subset_extremePoints hx, hx.1.2⟩
    · rintro ⟨hx, hi⟩
      have hx' : x ∈ (poly q).extremePoints ℝ := hv.symm ▸ hx
      refine ⟨⟨hx'.1, hi⟩, ?_⟩
      intro y hy z hz hseg
      exact hx'.2 hy.1 hz.1 hseg
  have h := closure_convexHull_extremePoints hcomp hconv
  rw [he, (((Set.finite_range p).subset (fun _ h => h.1)).isClosed_convexHull ℝ).closure_eq] at h
  exact h.symm
end FullereneGeometry
