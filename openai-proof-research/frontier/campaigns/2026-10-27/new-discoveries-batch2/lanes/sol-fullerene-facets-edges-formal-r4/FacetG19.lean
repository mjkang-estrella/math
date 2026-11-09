import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG19v07 : pG 7 ∈ facetSection qG 19 := by
 refine ⟨(facet_listed_vertices_G 7).1, ?_⟩
 exact (real_incidence_G 19 7).mp (by decide +kernel)
theorem onG19v08 : pG 8 ∈ facetSection qG 19 := by
 refine ⟨(facet_listed_vertices_G 8).1, ?_⟩
 exact (real_incidence_G 19 8).mp (by decide +kernel)
theorem onG19v21 : pG 21 ∈ facetSection qG 19 := by
 refine ⟨(facet_listed_vertices_G 21).1, ?_⟩
 exact (real_incidence_G 19 21).mp (by decide +kernel)
theorem dimension_G19 : affineDimension (facetSection qG 19) = 2 :=
 section_dimension_eq_of_minor qG 19 (pG 7) (pG 8) (pG 21)
  onG19v07 onG19v08 onG19v21 0 1 (by
   rw [← TripleCertificates.pbindG 7, ← TripleCertificates.pbindG 8, ← TripleCertificates.pbindG 21]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 7)
    (TripleCertificates.positiveG 8) (TripleCertificates.positiveG 21) 0 1 (by decide +kernel))
end FullereneGeometry
