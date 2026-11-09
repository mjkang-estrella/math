import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH13v01 : pH 1 ∈ facetSection qH 13 := by
 refine ⟨(facet_listed_vertices_H 1).1, ?_⟩
 exact (real_incidence_H 13 1).mp (by decide +kernel)
theorem onH13v02 : pH 2 ∈ facetSection qH 13 := by
 refine ⟨(facet_listed_vertices_H 2).1, ?_⟩
 exact (real_incidence_H 13 2).mp (by decide +kernel)
theorem onH13v11 : pH 11 ∈ facetSection qH 13 := by
 refine ⟨(facet_listed_vertices_H 11).1, ?_⟩
 exact (real_incidence_H 13 11).mp (by decide +kernel)
theorem dimension_H13 : affineDimension (facetSection qH 13) = 2 :=
 section_dimension_eq_of_minor qH 13 (pH 1) (pH 2) (pH 11)
  onH13v01 onH13v02 onH13v11 0 1 (by
   rw [← TripleCertificates.pbindH 1, ← TripleCertificates.pbindH 2, ← TripleCertificates.pbindH 11]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 1)
    (TripleCertificates.positiveH 2) (TripleCertificates.positiveH 11) 0 1 (by decide +kernel))
end FullereneGeometry
