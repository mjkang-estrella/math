import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG21v30 : pG 30 ∈ facetSection qG 21 := by
 refine ⟨(facet_listed_vertices_G 30).1, ?_⟩
 exact (real_incidence_G 21 30).mp (by decide +kernel)
theorem onG21v31 : pG 31 ∈ facetSection qG 21 := by
 refine ⟨(facet_listed_vertices_G 31).1, ?_⟩
 exact (real_incidence_G 21 31).mp (by decide +kernel)
theorem onG21v35 : pG 35 ∈ facetSection qG 21 := by
 refine ⟨(facet_listed_vertices_G 35).1, ?_⟩
 exact (real_incidence_G 21 35).mp (by decide +kernel)
theorem dimension_G21 : affineDimension (facetSection qG 21) = 2 :=
 section_dimension_eq_of_minor qG 21 (pG 30) (pG 31) (pG 35)
  onG21v30 onG21v31 onG21v35 0 1 (by
   rw [← TripleCertificates.pbindG 30, ← TripleCertificates.pbindG 31, ← TripleCertificates.pbindG 35]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 30)
    (TripleCertificates.positiveG 31) (TripleCertificates.positiveG 35) 0 1 (by decide +kernel))
end FullereneGeometry
