import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG20v22 : pG 22 ∈ facetSection qG 20 := by
 refine ⟨(facet_listed_vertices_G 22).1, ?_⟩
 exact (real_incidence_G 20 22).mp (by decide +kernel)
theorem onG20v25 : pG 25 ∈ facetSection qG 20 := by
 refine ⟨(facet_listed_vertices_G 25).1, ?_⟩
 exact (real_incidence_G 20 25).mp (by decide +kernel)
theorem onG20v29 : pG 29 ∈ facetSection qG 20 := by
 refine ⟨(facet_listed_vertices_G 29).1, ?_⟩
 exact (real_incidence_G 20 29).mp (by decide +kernel)
theorem dimension_G20 : affineDimension (facetSection qG 20) = 2 :=
 section_dimension_eq_of_minor qG 20 (pG 22) (pG 25) (pG 29)
  onG20v22 onG20v25 onG20v29 0 1 (by
   rw [← TripleCertificates.pbindG 22, ← TripleCertificates.pbindG 25, ← TripleCertificates.pbindG 29]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 22)
    (TripleCertificates.positiveG 25) (TripleCertificates.positiveG 29) 0 1 (by decide +kernel))
end FullereneGeometry
