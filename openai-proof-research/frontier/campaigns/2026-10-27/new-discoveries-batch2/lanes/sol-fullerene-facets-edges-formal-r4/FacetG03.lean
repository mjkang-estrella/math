import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG03v29 : pG 29 ∈ facetSection qG 3 := by
 refine ⟨(facet_listed_vertices_G 29).1, ?_⟩
 exact (real_incidence_G 3 29).mp (by decide +kernel)
theorem onG03v30 : pG 30 ∈ facetSection qG 3 := by
 refine ⟨(facet_listed_vertices_G 30).1, ?_⟩
 exact (real_incidence_G 3 30).mp (by decide +kernel)
theorem onG03v32 : pG 32 ∈ facetSection qG 3 := by
 refine ⟨(facet_listed_vertices_G 32).1, ?_⟩
 exact (real_incidence_G 3 32).mp (by decide +kernel)
theorem dimension_G03 : affineDimension (facetSection qG 3) = 2 :=
 section_dimension_eq_of_minor qG 3 (pG 29) (pG 30) (pG 32)
  onG03v29 onG03v30 onG03v32 0 1 (by
   rw [← TripleCertificates.pbindG 29, ← TripleCertificates.pbindG 30, ← TripleCertificates.pbindG 32]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 29)
    (TripleCertificates.positiveG 30) (TripleCertificates.positiveG 32) 0 1 (by decide +kernel))
end FullereneGeometry
