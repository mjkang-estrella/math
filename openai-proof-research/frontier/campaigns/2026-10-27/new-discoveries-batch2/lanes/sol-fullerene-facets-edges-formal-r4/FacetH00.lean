import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH00v00 : pH 0 ∈ facetSection qH 0 := by
 refine ⟨(facet_listed_vertices_H 0).1, ?_⟩
 exact (real_incidence_H 0 0).mp (by decide +kernel)
theorem onH00v01 : pH 1 ∈ facetSection qH 0 := by
 refine ⟨(facet_listed_vertices_H 1).1, ?_⟩
 exact (real_incidence_H 0 1).mp (by decide +kernel)
theorem onH00v02 : pH 2 ∈ facetSection qH 0 := by
 refine ⟨(facet_listed_vertices_H 2).1, ?_⟩
 exact (real_incidence_H 0 2).mp (by decide +kernel)
theorem dimension_H00 : affineDimension (facetSection qH 0) = 2 :=
 section_dimension_eq_of_minor qH 0 (pH 0) (pH 1) (pH 2)
  onH00v00 onH00v01 onH00v02 0 1 (by
   rw [← TripleCertificates.pbindH 0, ← TripleCertificates.pbindH 1, ← TripleCertificates.pbindH 2]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 0)
    (TripleCertificates.positiveH 1) (TripleCertificates.positiveH 2) 0 1 (by decide +kernel))
end FullereneGeometry
