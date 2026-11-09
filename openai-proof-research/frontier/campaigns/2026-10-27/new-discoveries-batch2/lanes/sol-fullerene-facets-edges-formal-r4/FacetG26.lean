import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG26v41 : pG 41 ∈ facetSection qG 26 := by
 refine ⟨(facet_listed_vertices_G 41).1, ?_⟩
 exact (real_incidence_G 26 41).mp (by decide +kernel)
theorem onG26v43 : pG 43 ∈ facetSection qG 26 := by
 refine ⟨(facet_listed_vertices_G 43).1, ?_⟩
 exact (real_incidence_G 26 43).mp (by decide +kernel)
theorem onG26v49 : pG 49 ∈ facetSection qG 26 := by
 refine ⟨(facet_listed_vertices_G 49).1, ?_⟩
 exact (real_incidence_G 26 49).mp (by decide +kernel)
theorem dimension_G26 : affineDimension (facetSection qG 26) = 2 :=
 section_dimension_eq_of_minor qG 26 (pG 41) (pG 43) (pG 49)
  onG26v41 onG26v43 onG26v49 0 1 (by
   rw [← TripleCertificates.pbindG 41, ← TripleCertificates.pbindG 43, ← TripleCertificates.pbindG 49]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 41)
    (TripleCertificates.positiveG 43) (TripleCertificates.positiveG 49) 0 1 (by decide +kernel))
end FullereneGeometry
