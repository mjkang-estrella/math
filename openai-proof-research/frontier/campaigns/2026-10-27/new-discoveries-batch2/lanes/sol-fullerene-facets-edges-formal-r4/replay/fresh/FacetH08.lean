import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH08v10 : pH 10 ∈ facetSection qH 8 := by
 refine ⟨(facet_listed_vertices_H 10).1, ?_⟩
 exact (real_incidence_H 8 10).mp (by decide +kernel)
theorem onH08v11 : pH 11 ∈ facetSection qH 8 := by
 refine ⟨(facet_listed_vertices_H 11).1, ?_⟩
 exact (real_incidence_H 8 11).mp (by decide +kernel)
theorem onH08v14 : pH 14 ∈ facetSection qH 8 := by
 refine ⟨(facet_listed_vertices_H 14).1, ?_⟩
 exact (real_incidence_H 8 14).mp (by decide +kernel)
theorem dimension_H08 : affineDimension (facetSection qH 8) = 2 :=
 section_dimension_eq_of_minor qH 8 (pH 10) (pH 11) (pH 14)
  onH08v10 onH08v11 onH08v14 0 1 (by
   rw [← TripleCertificates.pbindH 10, ← TripleCertificates.pbindH 11, ← TripleCertificates.pbindH 14]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 10)
    (TripleCertificates.positiveH 11) (TripleCertificates.positiveH 14) 0 1 (by decide +kernel))
end FullereneGeometry
