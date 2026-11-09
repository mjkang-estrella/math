import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG30v47 : pG 47 ∈ facetSection qG 30 := by
 refine ⟨(facet_listed_vertices_G 47).1, ?_⟩
 exact (real_incidence_G 30 47).mp (by decide +kernel)
theorem onG30v48 : pG 48 ∈ facetSection qG 30 := by
 refine ⟨(facet_listed_vertices_G 48).1, ?_⟩
 exact (real_incidence_G 30 48).mp (by decide +kernel)
theorem onG30v56 : pG 56 ∈ facetSection qG 30 := by
 refine ⟨(facet_listed_vertices_G 56).1, ?_⟩
 exact (real_incidence_G 30 56).mp (by decide +kernel)
theorem dimension_G30 : affineDimension (facetSection qG 30) = 2 :=
 section_dimension_eq_of_minor qG 30 (pG 47) (pG 48) (pG 56)
  onG30v47 onG30v48 onG30v56 0 1 (by
   rw [← TripleCertificates.pbindG 47, ← TripleCertificates.pbindG 48, ← TripleCertificates.pbindG 56]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 47)
    (TripleCertificates.positiveG 48) (TripleCertificates.positiveG 56) 0 1 (by decide +kernel))
end FullereneGeometry
