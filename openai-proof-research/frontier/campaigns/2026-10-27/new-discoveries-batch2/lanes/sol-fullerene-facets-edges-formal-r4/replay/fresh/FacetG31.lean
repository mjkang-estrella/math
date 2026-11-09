import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG31v15 : pG 15 ∈ facetSection qG 31 := by
 refine ⟨(facet_listed_vertices_G 15).1, ?_⟩
 exact (real_incidence_G 31 15).mp (by decide +kernel)
theorem onG31v17 : pG 17 ∈ facetSection qG 31 := by
 refine ⟨(facet_listed_vertices_G 17).1, ?_⟩
 exact (real_incidence_G 31 17).mp (by decide +kernel)
theorem onG31v54 : pG 54 ∈ facetSection qG 31 := by
 refine ⟨(facet_listed_vertices_G 54).1, ?_⟩
 exact (real_incidence_G 31 54).mp (by decide +kernel)
theorem dimension_G31 : affineDimension (facetSection qG 31) = 2 :=
 section_dimension_eq_of_minor qG 31 (pG 15) (pG 17) (pG 54)
  onG31v15 onG31v17 onG31v54 0 1 (by
   rw [← TripleCertificates.pbindG 15, ← TripleCertificates.pbindG 17, ← TripleCertificates.pbindG 54]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 15)
    (TripleCertificates.positiveG 17) (TripleCertificates.positiveG 54) 0 1 (by decide +kernel))
end FullereneGeometry
