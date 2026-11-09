import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG22v26 : pG 26 ∈ facetSection qG 22 := by
 refine ⟨(facet_listed_vertices_G 26).1, ?_⟩
 exact (real_incidence_G 22 26).mp (by decide +kernel)
theorem onG22v27 : pG 27 ∈ facetSection qG 22 := by
 refine ⟨(facet_listed_vertices_G 27).1, ?_⟩
 exact (real_incidence_G 22 27).mp (by decide +kernel)
theorem onG22v31 : pG 31 ∈ facetSection qG 22 := by
 refine ⟨(facet_listed_vertices_G 31).1, ?_⟩
 exact (real_incidence_G 22 31).mp (by decide +kernel)
theorem dimension_G22 : affineDimension (facetSection qG 22) = 2 :=
 section_dimension_eq_of_minor qG 22 (pG 26) (pG 27) (pG 31)
  onG22v26 onG22v27 onG22v31 0 1 (by
   rw [← TripleCertificates.pbindG 26, ← TripleCertificates.pbindG 27, ← TripleCertificates.pbindG 31]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 26)
    (TripleCertificates.positiveG 27) (TripleCertificates.positiveG 31) 0 1 (by decide +kernel))
end FullereneGeometry
