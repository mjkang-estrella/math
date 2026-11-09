import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG10v44 : pG 44 ∈ facetSection qG 10 := by
 refine ⟨(facet_listed_vertices_G 44).1, ?_⟩
 exact (real_incidence_G 10 44).mp (by decide +kernel)
theorem onG10v45 : pG 45 ∈ facetSection qG 10 := by
 refine ⟨(facet_listed_vertices_G 45).1, ?_⟩
 exact (real_incidence_G 10 45).mp (by decide +kernel)
theorem onG10v48 : pG 48 ∈ facetSection qG 10 := by
 refine ⟨(facet_listed_vertices_G 48).1, ?_⟩
 exact (real_incidence_G 10 48).mp (by decide +kernel)
theorem dimension_G10 : affineDimension (facetSection qG 10) = 2 :=
 section_dimension_eq_of_minor qG 10 (pG 44) (pG 45) (pG 48)
  onG10v44 onG10v45 onG10v48 0 1 (by
   rw [← TripleCertificates.pbindG 44, ← TripleCertificates.pbindG 45, ← TripleCertificates.pbindG 48]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 44)
    (TripleCertificates.positiveG 45) (TripleCertificates.positiveG 48) 0 1 (by decide +kernel))
end FullereneGeometry
