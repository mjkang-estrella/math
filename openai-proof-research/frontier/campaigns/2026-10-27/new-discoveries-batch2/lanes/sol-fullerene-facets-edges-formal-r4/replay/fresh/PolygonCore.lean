import FacetDimension
import IncidenceCore
import Mathlib.Analysis.Convex.Exposed
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace FullereneGeometry

/-- A convex real polygon with exactly `k` actual extreme vertices. -/
def ConvexPolygon (F : Set E) (k : ℕ) : Prop :=
  IsCompact F ∧ Convex ℝ F ∧ affineDimension F = 2 ∧
  (F.extremePoints ℝ).Finite ∧ F = convexHull ℝ (F.extremePoints ℝ) ∧
  (F.extremePoints ℝ).ncard = k

theorem section_compact {n : ℕ} (q : Fin n → E)
    (hc : IsCompact (poly q)) (i : Fin n) : IsCompact (facetSection q i) :=
  hc.of_isClosed_subset
    ((poly_closed q).inter (isClosed_eq (dot_continuous (q i)) continuous_const))
    (fun _ h => h.1)

theorem geometricFacet_isExposed {P F : Set E} (hf : GeometricFacet P F) :
    IsExposed ℝ P F := by
  obtain ⟨l,c,_,hb,he,⟨x,hx⟩,_⟩ := hf
  have hx' : x ∈ {z ∈ P | l z = c} := he ▸ hx
  intro _
  have hlx (y : E) : l y = dot (fun i => l (Pi.single i 1)) y := by
    have hy : y = ∑ i : Fin 3, y i • Pi.single i (1:ℝ) := by
      ext k; fin_cases k <;> simp [Pi.single_apply]
    conv_lhs => rw [hy]
    rw [map_sum]
    simp only [map_smul,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    change y i * l (Pi.single i 1) = l (Pi.single i 1) * y i
    ring
  have hlc : Continuous (l : E → ℝ) := by
    have h : (l : E → ℝ) = dot (fun i => l (Pi.single i 1)) := funext hlx
    rw [h]; exact dot_continuous _
  let lc : E →L[ℝ] ℝ := { toLinearMap := l, cont := hlc }
  refine ⟨lc,?_⟩
  rw [he]
  ext y
  constructor
  · rintro ⟨hy,hly⟩
    exact ⟨hy,fun z hz => by change l z ≤ l y; rw [hly]; exact hb z hz⟩
  · rintro ⟨hy,hmax⟩
    refine ⟨hy,le_antisymm (hb y hy) ?_⟩
    have h := hmax x hx'.1
    change l x ≤ l y at h
    rwa [hx'.2] at h
end FullereneGeometry
