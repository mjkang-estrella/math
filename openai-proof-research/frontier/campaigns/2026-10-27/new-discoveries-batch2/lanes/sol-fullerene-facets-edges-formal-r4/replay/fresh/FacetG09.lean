import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG09v37 : pG 37 ∈ facetSection qG 9 := by
 refine ⟨(facet_listed_vertices_G 37).1, ?_⟩
 exact (real_incidence_G 9 37).mp (by decide +kernel)
theorem onG09v38 : pG 38 ∈ facetSection qG 9 := by
 refine ⟨(facet_listed_vertices_G 38).1, ?_⟩
 exact (real_incidence_G 9 38).mp (by decide +kernel)
theorem onG09v40 : pG 40 ∈ facetSection qG 9 := by
 refine ⟨(facet_listed_vertices_G 40).1, ?_⟩
 exact (real_incidence_G 9 40).mp (by decide +kernel)
theorem dimension_G09 : affineDimension (facetSection qG 9) = 2 :=
 section_dimension_eq_of_minor qG 9 (pG 37) (pG 38) (pG 40)
  onG09v37 onG09v38 onG09v40 0 1 (by
   rw [← TripleCertificates.pbindG 37, ← TripleCertificates.pbindG 38, ← TripleCertificates.pbindG 40]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 37)
    (TripleCertificates.positiveG 38) (TripleCertificates.positiveG 40) 0 1 (by decide +kernel))
end FullereneGeometry
