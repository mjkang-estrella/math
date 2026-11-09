import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG18v06 : pG 6 ∈ facetSection qG 18 := by
 refine ⟨(facet_listed_vertices_G 6).1, ?_⟩
 exact (real_incidence_G 18 6).mp (by decide +kernel)
theorem onG18v09 : pG 9 ∈ facetSection qG 18 := by
 refine ⟨(facet_listed_vertices_G 9).1, ?_⟩
 exact (real_incidence_G 18 9).mp (by decide +kernel)
theorem onG18v10 : pG 10 ∈ facetSection qG 18 := by
 refine ⟨(facet_listed_vertices_G 10).1, ?_⟩
 exact (real_incidence_G 18 10).mp (by decide +kernel)
theorem dimension_G18 : affineDimension (facetSection qG 18) = 2 :=
 section_dimension_eq_of_minor qG 18 (pG 6) (pG 9) (pG 10)
  onG18v06 onG18v09 onG18v10 0 1 (by
   rw [← TripleCertificates.pbindG 6, ← TripleCertificates.pbindG 9, ← TripleCertificates.pbindG 10]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 6)
    (TripleCertificates.positiveG 9) (TripleCertificates.positiveG 10) 0 1 (by decide +kernel))
end FullereneGeometry
