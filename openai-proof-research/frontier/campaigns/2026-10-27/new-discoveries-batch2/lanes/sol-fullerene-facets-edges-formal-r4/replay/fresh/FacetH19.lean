import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH19v07 : pH 7 ∈ facetSection qH 19 := by
 refine ⟨(facet_listed_vertices_H 7).1, ?_⟩
 exact (real_incidence_H 19 7).mp (by decide +kernel)
theorem onH19v08 : pH 8 ∈ facetSection qH 19 := by
 refine ⟨(facet_listed_vertices_H 8).1, ?_⟩
 exact (real_incidence_H 19 8).mp (by decide +kernel)
theorem onH19v21 : pH 21 ∈ facetSection qH 19 := by
 refine ⟨(facet_listed_vertices_H 21).1, ?_⟩
 exact (real_incidence_H 19 21).mp (by decide +kernel)
theorem dimension_H19 : affineDimension (facetSection qH 19) = 2 :=
 section_dimension_eq_of_minor qH 19 (pH 7) (pH 8) (pH 21)
  onH19v07 onH19v08 onH19v21 0 1 (by
   rw [← TripleCertificates.pbindH 7, ← TripleCertificates.pbindH 8, ← TripleCertificates.pbindH 21]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 7)
    (TripleCertificates.positiveH 8) (TripleCertificates.positiveH 21) 0 1 (by decide +kernel))
end FullereneGeometry
