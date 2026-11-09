import FeasibleG
import IncidenceRealG
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onG24v33 : pG 33 ∈ facetSection qG 24 := by
 refine ⟨(facet_listed_vertices_G 33).1, ?_⟩
 exact (real_incidence_G 24 33).mp (by decide +kernel)
theorem onG24v34 : pG 34 ∈ facetSection qG 24 := by
 refine ⟨(facet_listed_vertices_G 34).1, ?_⟩
 exact (real_incidence_G 24 34).mp (by decide +kernel)
theorem onG24v42 : pG 42 ∈ facetSection qG 24 := by
 refine ⟨(facet_listed_vertices_G 42).1, ?_⟩
 exact (real_incidence_G 24 42).mp (by decide +kernel)
theorem dimension_G24 : affineDimension (facetSection qG 24) = 2 :=
 section_dimension_eq_of_minor qG 24 (pG 33) (pG 34) (pG 42)
  onG24v33 onG24v34 onG24v42 0 1 (by
   rw [← TripleCertificates.pbindG 33, ← TripleCertificates.pbindG 34, ← TripleCertificates.pbindG 42]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveG 33)
    (TripleCertificates.positiveG 34) (TripleCertificates.positiveG 42) 0 1 (by decide +kernel))
end FullereneGeometry
