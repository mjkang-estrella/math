import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH21v31 : pH 31 ∈ facetSection qH 21 := by
 refine ⟨(facet_listed_vertices_H 31).1, ?_⟩
 exact (real_incidence_H 21 31).mp (by decide +kernel)
theorem onH21v32 : pH 32 ∈ facetSection qH 21 := by
 refine ⟨(facet_listed_vertices_H 32).1, ?_⟩
 exact (real_incidence_H 21 32).mp (by decide +kernel)
theorem onH21v36 : pH 36 ∈ facetSection qH 21 := by
 refine ⟨(facet_listed_vertices_H 36).1, ?_⟩
 exact (real_incidence_H 21 36).mp (by decide +kernel)
theorem dimension_H21 : affineDimension (facetSection qH 21) = 2 :=
 section_dimension_eq_of_minor qH 21 (pH 31) (pH 32) (pH 36)
  onH21v31 onH21v32 onH21v36 0 1 (by
   rw [← TripleCertificates.pbindH 31, ← TripleCertificates.pbindH 32, ← TripleCertificates.pbindH 36]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 31)
    (TripleCertificates.positiveH 32) (TripleCertificates.positiveH 36) 0 1 (by decide +kernel))
end FullereneGeometry
