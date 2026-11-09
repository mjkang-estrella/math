import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG29v12 : pG 12 ∈ facetSection qG 29 := by
 refine ⟨(facet_listed_vertices_G 12).1, ?_⟩
 exact (real_incidence_G 29 12).mp (by decide +kernel)
theorem onG29v14 : pG 14 ∈ facetSection qG 29 := by
 refine ⟨(facet_listed_vertices_G 14).1, ?_⟩
 exact (real_incidence_G 29 14).mp (by decide +kernel)
theorem onG29v39 : pG 39 ∈ facetSection qG 29 := by
 refine ⟨(facet_listed_vertices_G 39).1, ?_⟩
 exact (real_incidence_G 29 39).mp (by decide +kernel)
theorem dimension_G29 : affineDimension (facetSection qG 29) = 2 :=
 section_dimension_eq_of_minor qG 29 (pG 12) (pG 14) (pG 39)
  onG29v12 onG29v14 onG29v39 0 1 (by
   rw [← TripleCertificates.pbindG 12, ← TripleCertificates.pbindG 14, ← TripleCertificates.pbindG 39]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 12)
    (TripleCertificates.positiveG 14) (TripleCertificates.positiveG 39) 0 1 (by decide +kernel))
end FullereneGeometry
