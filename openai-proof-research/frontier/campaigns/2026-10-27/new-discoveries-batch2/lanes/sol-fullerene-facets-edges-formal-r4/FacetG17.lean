import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG17v08 : pG 8 ∈ facetSection qG 17 := by
 refine ⟨(facet_listed_vertices_G 8).1, ?_⟩
 exact (real_incidence_G 17 8).mp (by decide +kernel)
theorem onG17v09 : pG 9 ∈ facetSection qG 17 := by
 refine ⟨(facet_listed_vertices_G 9).1, ?_⟩
 exact (real_incidence_G 17 9).mp (by decide +kernel)
theorem onG17v22 : pG 22 ∈ facetSection qG 17 := by
 refine ⟨(facet_listed_vertices_G 22).1, ?_⟩
 exact (real_incidence_G 17 22).mp (by decide +kernel)
theorem dimension_G17 : affineDimension (facetSection qG 17) = 2 :=
 section_dimension_eq_of_minor qG 17 (pG 8) (pG 9) (pG 22)
  onG17v08 onG17v09 onG17v22 0 1 (by
   rw [← TripleCertificates.pbindG 8, ← TripleCertificates.pbindG 9, ← TripleCertificates.pbindG 22]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 8)
    (TripleCertificates.positiveG 9) (TripleCertificates.positiveG 22) 0 1 (by decide +kernel))
end FullereneGeometry
