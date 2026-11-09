import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH06v24 : pH 24 ∈ facetSection qH 6 := by
 refine ⟨(facet_listed_vertices_H 24).1, ?_⟩
 exact (real_incidence_H 6 24).mp (by decide +kernel)
theorem onH06v25 : pH 25 ∈ facetSection qH 6 := by
 refine ⟨(facet_listed_vertices_H 25).1, ?_⟩
 exact (real_incidence_H 6 25).mp (by decide +kernel)
theorem onH06v29 : pH 29 ∈ facetSection qH 6 := by
 refine ⟨(facet_listed_vertices_H 29).1, ?_⟩
 exact (real_incidence_H 6 29).mp (by decide +kernel)
theorem dimension_H06 : affineDimension (facetSection qH 6) = 2 :=
 section_dimension_eq_of_minor qH 6 (pH 24) (pH 25) (pH 29)
  onH06v24 onH06v25 onH06v29 0 1 (by
   rw [← TripleCertificates.pbindH 24, ← TripleCertificates.pbindH 25, ← TripleCertificates.pbindH 29]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 24)
    (TripleCertificates.positiveH 25) (TripleCertificates.positiveH 29) 0 1 (by decide +kernel))
end FullereneGeometry
