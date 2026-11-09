import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG01v00 : pG 0 ∈ facetSection qG 1 := by
 refine ⟨(facet_listed_vertices_G 0).1, ?_⟩
 exact (real_incidence_G 1 0).mp (by decide +kernel)
theorem onG01v05 : pG 5 ∈ facetSection qG 1 := by
 refine ⟨(facet_listed_vertices_G 5).1, ?_⟩
 exact (real_incidence_G 1 5).mp (by decide +kernel)
theorem onG01v06 : pG 6 ∈ facetSection qG 1 := by
 refine ⟨(facet_listed_vertices_G 6).1, ?_⟩
 exact (real_incidence_G 1 6).mp (by decide +kernel)
theorem dimension_G01 : affineDimension (facetSection qG 1) = 2 :=
 section_dimension_eq_of_minor qG 1 (pG 0) (pG 5) (pG 6)
  onG01v00 onG01v05 onG01v06 0 1 (by
   rw [← TripleCertificates.pbindG 0, ← TripleCertificates.pbindG 5, ← TripleCertificates.pbindG 6]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 0)
    (TripleCertificates.positiveG 5) (TripleCertificates.positiveG 6) 0 1 (by decide +kernel))
end FullereneGeometry
