import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG23v32 : pG 32 ∈ facetSection qG 23 := by
 refine ⟨(facet_listed_vertices_G 32).1, ?_⟩
 exact (real_incidence_G 23 32).mp (by decide +kernel)
theorem onG23v33 : pG 33 ∈ facetSection qG 23 := by
 refine ⟨(facet_listed_vertices_G 33).1, ?_⟩
 exact (real_incidence_G 23 33).mp (by decide +kernel)
theorem onG23v36 : pG 36 ∈ facetSection qG 23 := by
 refine ⟨(facet_listed_vertices_G 36).1, ?_⟩
 exact (real_incidence_G 23 36).mp (by decide +kernel)
theorem dimension_G23 : affineDimension (facetSection qG 23) = 2 :=
 section_dimension_eq_of_minor qG 23 (pG 32) (pG 33) (pG 36)
  onG23v32 onG23v33 onG23v36 0 1 (by
   rw [← TripleCertificates.pbindG 32, ← TripleCertificates.pbindG 33, ← TripleCertificates.pbindG 36]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 32)
    (TripleCertificates.positiveG 33) (TripleCertificates.positiveG 36) 0 1 (by decide +kernel))
end FullereneGeometry
