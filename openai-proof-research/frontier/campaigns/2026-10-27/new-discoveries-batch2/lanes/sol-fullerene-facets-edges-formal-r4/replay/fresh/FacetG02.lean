import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG02v22 : pG 22 ∈ facetSection qG 2 := by
 refine ⟨(facet_listed_vertices_G 22).1, ?_⟩
 exact (real_incidence_G 2 22).mp (by decide +kernel)
theorem onG02v23 : pG 23 ∈ facetSection qG 2 := by
 refine ⟨(facet_listed_vertices_G 23).1, ?_⟩
 exact (real_incidence_G 2 23).mp (by decide +kernel)
theorem onG02v27 : pG 27 ∈ facetSection qG 2 := by
 refine ⟨(facet_listed_vertices_G 27).1, ?_⟩
 exact (real_incidence_G 2 27).mp (by decide +kernel)
theorem dimension_G02 : affineDimension (facetSection qG 2) = 2 :=
 section_dimension_eq_of_minor qG 2 (pG 22) (pG 23) (pG 27)
  onG02v22 onG02v23 onG02v27 0 1 (by
   rw [← TripleCertificates.pbindG 22, ← TripleCertificates.pbindG 23, ← TripleCertificates.pbindG 27]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 22)
    (TripleCertificates.positiveG 23) (TripleCertificates.positiveG 27) 0 1 (by decide +kernel))
end FullereneGeometry
