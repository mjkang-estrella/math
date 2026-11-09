import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG07v12 : pG 12 ∈ facetSection qG 7 := by
 refine ⟨(facet_listed_vertices_G 12).1, ?_⟩
 exact (real_incidence_G 7 12).mp (by decide +kernel)
theorem onG07v13 : pG 13 ∈ facetSection qG 7 := by
 refine ⟨(facet_listed_vertices_G 13).1, ?_⟩
 exact (real_incidence_G 7 13).mp (by decide +kernel)
theorem onG07v17 : pG 17 ∈ facetSection qG 7 := by
 refine ⟨(facet_listed_vertices_G 17).1, ?_⟩
 exact (real_incidence_G 7 17).mp (by decide +kernel)
theorem dimension_G07 : affineDimension (facetSection qG 7) = 2 :=
 section_dimension_eq_of_minor qG 7 (pG 12) (pG 13) (pG 17)
  onG07v12 onG07v13 onG07v17 0 1 (by
   rw [← TripleCertificates.pbindG 12, ← TripleCertificates.pbindG 13, ← TripleCertificates.pbindG 17]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 12)
    (TripleCertificates.positiveG 13) (TripleCertificates.positiveG 17) 0 1 (by decide +kernel))
end FullereneGeometry
