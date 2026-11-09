import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG25v34 : pG 34 ∈ facetSection qG 25 := by
 refine ⟨(facet_listed_vertices_G 34).1, ?_⟩
 exact (real_incidence_G 25 34).mp (by decide +kernel)
theorem onG25v35 : pG 35 ∈ facetSection qG 25 := by
 refine ⟨(facet_listed_vertices_G 35).1, ?_⟩
 exact (real_incidence_G 25 35).mp (by decide +kernel)
theorem onG25v37 : pG 37 ∈ facetSection qG 25 := by
 refine ⟨(facet_listed_vertices_G 37).1, ?_⟩
 exact (real_incidence_G 25 37).mp (by decide +kernel)
theorem dimension_G25 : affineDimension (facetSection qG 25) = 2 :=
 section_dimension_eq_of_minor qG 25 (pG 34) (pG 35) (pG 37)
  onG25v34 onG25v35 onG25v37 0 1 (by
   rw [← TripleCertificates.pbindG 34, ← TripleCertificates.pbindG 35, ← TripleCertificates.pbindG 37]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 34)
    (TripleCertificates.positiveG 35) (TripleCertificates.positiveG 37) 0 1 (by decide +kernel))
end FullereneGeometry
