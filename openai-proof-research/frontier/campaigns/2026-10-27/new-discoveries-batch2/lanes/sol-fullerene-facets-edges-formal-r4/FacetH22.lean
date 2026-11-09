import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH22v26 : pH 26 ∈ facetSection qH 22 := by
 refine ⟨(facet_listed_vertices_H 26).1, ?_⟩
 exact (real_incidence_H 22 26).mp (by decide +kernel)
theorem onH22v27 : pH 27 ∈ facetSection qH 22 := by
 refine ⟨(facet_listed_vertices_H 27).1, ?_⟩
 exact (real_incidence_H 22 27).mp (by decide +kernel)
theorem onH22v32 : pH 32 ∈ facetSection qH 22 := by
 refine ⟨(facet_listed_vertices_H 32).1, ?_⟩
 exact (real_incidence_H 22 32).mp (by decide +kernel)
theorem dimension_H22 : affineDimension (facetSection qH 22) = 2 :=
 section_dimension_eq_of_minor qH 22 (pH 26) (pH 27) (pH 32)
  onH22v26 onH22v27 onH22v32 0 1 (by
   rw [← TripleCertificates.pbindH 26, ← TripleCertificates.pbindH 27, ← TripleCertificates.pbindH 32]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 26)
    (TripleCertificates.positiveH 27) (TripleCertificates.positiveH 32) 0 1 (by decide +kernel))
end FullereneGeometry
