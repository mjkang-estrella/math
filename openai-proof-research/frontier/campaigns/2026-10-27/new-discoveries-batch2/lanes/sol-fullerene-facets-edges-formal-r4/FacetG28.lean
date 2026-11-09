import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG28v44 : pG 44 ∈ facetSection qG 28 := by
 refine ⟨(facet_listed_vertices_G 44).1, ?_⟩
 exact (real_incidence_G 28 44).mp (by decide +kernel)
theorem onG28v46 : pG 46 ∈ facetSection qG 28 := by
 refine ⟨(facet_listed_vertices_G 46).1, ?_⟩
 exact (real_incidence_G 28 46).mp (by decide +kernel)
theorem onG28v50 : pG 50 ∈ facetSection qG 28 := by
 refine ⟨(facet_listed_vertices_G 50).1, ?_⟩
 exact (real_incidence_G 28 50).mp (by decide +kernel)
theorem dimension_G28 : affineDimension (facetSection qG 28) = 2 :=
 section_dimension_eq_of_minor qG 28 (pG 44) (pG 46) (pG 50)
  onG28v44 onG28v46 onG28v50 0 1 (by
   rw [← TripleCertificates.pbindG 44, ← TripleCertificates.pbindG 46, ← TripleCertificates.pbindG 50]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 44)
    (TripleCertificates.positiveG 46) (TripleCertificates.positiveG 50) 0 1 (by decide +kernel))
end FullereneGeometry
