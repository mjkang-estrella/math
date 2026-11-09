import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG04v41 : pG 41 ∈ facetSection qG 4 := by
 refine ⟨(facet_listed_vertices_G 41).1, ?_⟩
 exact (real_incidence_G 4 41).mp (by decide +kernel)
theorem onG04v42 : pG 42 ∈ facetSection qG 4 := by
 refine ⟨(facet_listed_vertices_G 42).1, ?_⟩
 exact (real_incidence_G 4 42).mp (by decide +kernel)
theorem onG04v46 : pG 46 ∈ facetSection qG 4 := by
 refine ⟨(facet_listed_vertices_G 46).1, ?_⟩
 exact (real_incidence_G 4 46).mp (by decide +kernel)
theorem dimension_G04 : affineDimension (facetSection qG 4) = 2 :=
 section_dimension_eq_of_minor qG 4 (pG 41) (pG 42) (pG 46)
  onG04v41 onG04v42 onG04v46 0 1 (by
   rw [← TripleCertificates.pbindG 41, ← TripleCertificates.pbindG 42, ← TripleCertificates.pbindG 46]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 41)
    (TripleCertificates.positiveG 42) (TripleCertificates.positiveG 46) 0 1 (by decide +kernel))
end FullereneGeometry
