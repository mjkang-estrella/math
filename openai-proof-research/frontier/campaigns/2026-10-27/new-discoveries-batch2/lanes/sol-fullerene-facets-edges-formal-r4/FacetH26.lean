import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH26v28 : pH 28 ∈ facetSection qH 26 := by
 refine ⟨(facet_listed_vertices_H 28).1, ?_⟩
 exact (real_incidence_H 26 28).mp (by decide +kernel)
theorem onH26v29 : pH 29 ∈ facetSection qH 26 := by
 refine ⟨(facet_listed_vertices_H 29).1, ?_⟩
 exact (real_incidence_H 26 29).mp (by decide +kernel)
theorem onH26v42 : pH 42 ∈ facetSection qH 26 := by
 refine ⟨(facet_listed_vertices_H 42).1, ?_⟩
 exact (real_incidence_H 26 42).mp (by decide +kernel)
theorem dimension_H26 : affineDimension (facetSection qH 26) = 2 :=
 section_dimension_eq_of_minor qH 26 (pH 28) (pH 29) (pH 42)
  onH26v28 onH26v29 onH26v42 0 1 (by
   rw [← TripleCertificates.pbindH 28, ← TripleCertificates.pbindH 29, ← TripleCertificates.pbindH 42]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 28)
    (TripleCertificates.positiveH 29) (TripleCertificates.positiveH 42) 0 1 (by decide +kernel))
end FullereneGeometry
