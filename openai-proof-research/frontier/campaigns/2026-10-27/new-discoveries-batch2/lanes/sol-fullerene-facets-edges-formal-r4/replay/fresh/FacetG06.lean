import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG06v24 : pG 24 ∈ facetSection qG 6 := by
 refine ⟨(facet_listed_vertices_G 24).1, ?_⟩
 exact (real_incidence_G 6 24).mp (by decide +kernel)
theorem onG06v25 : pG 25 ∈ facetSection qG 6 := by
 refine ⟨(facet_listed_vertices_G 25).1, ?_⟩
 exact (real_incidence_G 6 25).mp (by decide +kernel)
theorem onG06v28 : pG 28 ∈ facetSection qG 6 := by
 refine ⟨(facet_listed_vertices_G 28).1, ?_⟩
 exact (real_incidence_G 6 28).mp (by decide +kernel)
theorem dimension_G06 : affineDimension (facetSection qG 6) = 2 :=
 section_dimension_eq_of_minor qG 6 (pG 24) (pG 25) (pG 28)
  onG06v24 onG06v25 onG06v28 0 1 (by
   rw [← TripleCertificates.pbindG 24, ← TripleCertificates.pbindG 25, ← TripleCertificates.pbindG 28]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 24)
    (TripleCertificates.positiveG 25) (TripleCertificates.positiveG 28) 0 1 (by decide +kernel))
end FullereneGeometry
