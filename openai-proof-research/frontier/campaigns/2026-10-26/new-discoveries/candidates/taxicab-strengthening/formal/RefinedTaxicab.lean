import StrengthenedScalar
import StrengtheningGeometry
import TaxicabGeometry

open TaxicabGeometry

namespace RefinedTaxicab

/-- The sharp taxicab inequality for any nonnegative barycentric point. -/
theorem barycentric_bound (la lb lc : ℝ) (A B C P : Point)
    (hAB : A≠B) (hBC : B≠C) (hCA : C≠A)
    (hla : 0≤la) (hlb : 0≤lb) (hlc : 0≤lc)
    (hsum : la+lb+lc=1) (hP : P=la • A+lb • B+lc • C) :
    3*(sideDistance P B C+sideDistance P C A+sideDistance P A B+min (sideDistance P B C) (min (sideDistance P C A) (sideDistance P A B))) ≤
      2*(norm1 (A-P)+norm1 (B-P)+norm1 (C-P)) := by
  obtain ⟨hu,hv,hw,hub,hvc,hwa,hau,hbv,hcw⟩ :=
    triangle_side_bounds la lb lc A B C P hAB hBC hCA hla hlb hlc hsum hP
  exact StrengthenedTaxicab.scalar_strength_weighted
    (norm1_nonneg _) (norm1_nonneg _) (norm1_nonneg _) hu hv hw
    (hub.trans (min_le_left _ _)) (hub.trans (min_le_right _ _))
    (hvc.trans (min_le_left _ _)) (hvc.trans (min_le_right _ _))
    (hwa.trans (min_le_left _ _)) (hwa.trans (min_le_right _ _))
    hla hlb hlc hsum hau hbv hcw

/-- A complete geometric statement over the ordinary closed triangle. -/
theorem convexHull_bound (A B C P : Point)
    (hAB : A≠B) (hBC : B≠C) (hCA : C≠A)
    (hP : P ∈ convexHull ℝ ({A,B,C} : Set Point)) :
    (3/2:ℝ)*(sideDistance P B C+sideDistance P C A+sideDistance P A B+min (sideDistance P B C) (min (sideDistance P C A) (sideDistance P A B))) ≤
      norm1 (A-P)+norm1 (B-P)+norm1 (C-P) := by
  classical
  have hPf : P ∈ convexHull ℝ (↑({A,B,C} : Finset Point) : Set Point) := by simpa using hP
  obtain ⟨f,hf,hs,hpoint⟩ := Finset.mem_convexHull'.mp hPf
  have hla : 0≤f A := hf A (by simp)
  have hlb : 0≤f B := hf B (by simp)
  have hlc : 0≤f C := hf C (by simp)
  have hsum : f A+f B+f C=1 := by
    simpa [hAB,hBC,hCA,Ne.symm hAB,Ne.symm hBC,Ne.symm hCA,add_assoc] using hs
  have hcomb : P=f A • A+f B • B+f C • C := by
    simpa [hAB,hBC,hCA,Ne.symm hAB,Ne.symm hBC,Ne.symm hCA,add_assoc] using hpoint.symm
  have h := barycentric_bound (f A) (f B) (f C) A B C P hAB hBC hCA hla hlb hlc hsum hcomb
  linarith

/-- The exact arbitrary-triangle interior assertion of MathDB341671. -/
theorem refined_interior_bound (A B C P : Point)
    (harea : area A B C≠0)
    (hP : P ∈ interior (convexHull ℝ ({A,B,C} : Set Point))) :
    (3/2:ℝ)*(sideDistance P B C+sideDistance P C A+sideDistance P A B+min (sideDistance P B C) (min (sideDistance P C A) (sideDistance P A B))) ≤
      norm1 (A-P)+norm1 (B-P)+norm1 (C-P) := by
  obtain ⟨hAB,hBC,hCA⟩ := area_distinct A B C harea
  exact convexHull_bound A B C P hAB hBC hCA (interior_subset hP)

/-- Exact original source conjecture, as a consequence of the refinement. -/
theorem source_conjecture_341671 (A B C P : Point)
    (harea : area A B C≠0)
    (hP : P ∈ interior (convexHull ℝ ({A,B,C} : Set Point))) :
    (3/2:ℝ)*(sideDistance P B C+sideDistance P C A+sideDistance P A B) ≤
      norm1 (A-P)+norm1 (B-P)+norm1 (C-P) := by
  have h := refined_interior_bound A B C P harea hP
  have hm : 0 ≤ min (sideDistance P B C) (min (sideDistance P C A) (sideDistance P A B)) := by
    exact le_min (lineDistance_nonneg _ _ _ _)
      (le_min (lineDistance_nonneg _ _ _ _) (lineDistance_nonneg _ _ _ _))
  linarith

/-- Outer coefficient3/2 is sharp at a fixed strictly interior configuration. -/
theorem outer_coefficient_sharp {K : ℝ} (hK : (3/2:ℝ)<K) :
    ∃ A B C P : Point, area A B C≠0 ∧
      P ∈ interior (convexHull ℝ ({A,B,C} : Set Point)) ∧
      norm1 (A-P)+norm1 (B-P)+norm1 (C-P) <
        K*(sideDistance P B C+sideDistance P C A+sideDistance P A B+
          min (sideDistance P B C) (min (sideDistance P C A) (sideDistance P A B))) := by
  refine ⟨StrengtheningGeometry.A,StrengtheningGeometry.B,StrengtheningGeometry.C,
    StrengtheningGeometry.P,StrengtheningGeometry.nondegenerate,StrengtheningGeometry.strictly_interior,?_⟩
  obtain ⟨ha,hb,hc⟩ := StrengtheningGeometry.vertex_sizes
  obtain ⟨hu,hv,hw⟩ := StrengtheningGeometry.side_distances
  rw [ha,hb,hc,hu,hv,hw]
  norm_num
  linarith

/-- With outer coefficient3/2 fixed, the minimum-side coefficient cannot exceed1. -/
theorem minimum_coefficient_sharp {K : ℝ} (hK : 1<K) :
    ∃ A B C P : Point, area A B C≠0 ∧
      P ∈ interior (convexHull ℝ ({A,B,C} : Set Point)) ∧
      norm1 (A-P)+norm1 (B-P)+norm1 (C-P) <
        (3/2:ℝ)*(sideDistance P B C+sideDistance P C A+sideDistance P A B+
          K*min (sideDistance P B C) (min (sideDistance P C A) (sideDistance P A B))) := by
  refine ⟨StrengtheningGeometry.A,StrengtheningGeometry.B,StrengtheningGeometry.C,
    StrengtheningGeometry.P,StrengtheningGeometry.nondegenerate,StrengtheningGeometry.strictly_interior,?_⟩
  obtain ⟨ha,hb,hc⟩ := StrengtheningGeometry.vertex_sizes
  obtain ⟨hu,hv,hw⟩ := StrengtheningGeometry.side_distances
  rw [ha,hb,hc,hu,hv,hw]
  norm_num
  linarith

#print axioms refined_interior_bound
#print axioms outer_coefficient_sharp
#print axioms minimum_coefficient_sharp
end RefinedTaxicab
