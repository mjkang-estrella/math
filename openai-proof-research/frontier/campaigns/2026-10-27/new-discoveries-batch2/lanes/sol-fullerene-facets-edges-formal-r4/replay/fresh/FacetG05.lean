import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG05v18 : pG 18 ∈ facetSection qG 5 := by
 refine ⟨(facet_listed_vertices_G 18).1, ?_⟩
 exact (real_incidence_G 5 18).mp (by decide +kernel)
theorem onG05v19 : pG 19 ∈ facetSection qG 5 := by
 refine ⟨(facet_listed_vertices_G 19).1, ?_⟩
 exact (real_incidence_G 5 19).mp (by decide +kernel)
theorem onG05v21 : pG 21 ∈ facetSection qG 5 := by
 refine ⟨(facet_listed_vertices_G 21).1, ?_⟩
 exact (real_incidence_G 5 21).mp (by decide +kernel)
theorem dimension_G05 : affineDimension (facetSection qG 5) = 2 :=
 section_dimension_eq_of_minor qG 5 (pG 18) (pG 19) (pG 21)
  onG05v18 onG05v19 onG05v21 0 1 (by
   rw [← TripleCertificates.pbindG 18, ← TripleCertificates.pbindG 19, ← TripleCertificates.pbindG 21]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 18)
    (TripleCertificates.positiveG 19) (TripleCertificates.positiveG 21) 0 1 (by decide +kernel))
end FullereneGeometry
