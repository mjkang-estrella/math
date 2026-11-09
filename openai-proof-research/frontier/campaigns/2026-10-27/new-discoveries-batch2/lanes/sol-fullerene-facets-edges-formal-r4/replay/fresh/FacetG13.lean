import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG13v01 : pG 1 ∈ facetSection qG 13 := by
 refine ⟨(facet_listed_vertices_G 1).1, ?_⟩
 exact (real_incidence_G 13 1).mp (by decide +kernel)
theorem onG13v02 : pG 2 ∈ facetSection qG 13 := by
 refine ⟨(facet_listed_vertices_G 2).1, ?_⟩
 exact (real_incidence_G 13 2).mp (by decide +kernel)
theorem onG13v11 : pG 11 ∈ facetSection qG 13 := by
 refine ⟨(facet_listed_vertices_G 11).1, ?_⟩
 exact (real_incidence_G 13 11).mp (by decide +kernel)
theorem dimension_G13 : affineDimension (facetSection qG 13) = 2 :=
 section_dimension_eq_of_minor qG 13 (pG 1) (pG 2) (pG 11)
  onG13v01 onG13v02 onG13v11 0 1 (by
   rw [← TripleCertificates.pbindG 1, ← TripleCertificates.pbindG 2, ← TripleCertificates.pbindG 11]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 1)
    (TripleCertificates.positiveG 2) (TripleCertificates.positiveG 11) 0 1 (by decide +kernel))
end FullereneGeometry
