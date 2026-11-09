import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG16v04 : pG 4 ∈ facetSection qG 16 := by
 refine ⟨(facet_listed_vertices_G 4).1, ?_⟩
 exact (real_incidence_G 16 4).mp (by decide +kernel)
theorem onG16v05 : pG 5 ∈ facetSection qG 16 := by
 refine ⟨(facet_listed_vertices_G 5).1, ?_⟩
 exact (real_incidence_G 16 5).mp (by decide +kernel)
theorem onG16v07 : pG 7 ∈ facetSection qG 16 := by
 refine ⟨(facet_listed_vertices_G 7).1, ?_⟩
 exact (real_incidence_G 16 7).mp (by decide +kernel)
theorem dimension_G16 : affineDimension (facetSection qG 16) = 2 :=
 section_dimension_eq_of_minor qG 16 (pG 4) (pG 5) (pG 7)
  onG16v04 onG16v05 onG16v07 0 1 (by
   rw [← TripleCertificates.pbindG 4, ← TripleCertificates.pbindG 5, ← TripleCertificates.pbindG 7]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 4)
    (TripleCertificates.positiveG 5) (TripleCertificates.positiveG 7) 0 1 (by decide +kernel))
end FullereneGeometry
