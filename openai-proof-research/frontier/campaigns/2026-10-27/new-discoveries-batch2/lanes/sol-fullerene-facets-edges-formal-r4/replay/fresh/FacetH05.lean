import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH05v18 : pH 18 ∈ facetSection qH 5 := by
 refine ⟨(facet_listed_vertices_H 18).1, ?_⟩
 exact (real_incidence_H 5 18).mp (by decide +kernel)
theorem onH05v19 : pH 19 ∈ facetSection qH 5 := by
 refine ⟨(facet_listed_vertices_H 19).1, ?_⟩
 exact (real_incidence_H 5 19).mp (by decide +kernel)
theorem onH05v21 : pH 21 ∈ facetSection qH 5 := by
 refine ⟨(facet_listed_vertices_H 21).1, ?_⟩
 exact (real_incidence_H 5 21).mp (by decide +kernel)
theorem dimension_H05 : affineDimension (facetSection qH 5) = 2 :=
 section_dimension_eq_of_minor qH 5 (pH 18) (pH 19) (pH 21)
  onH05v18 onH05v19 onH05v21 0 1 (by
   rw [← TripleCertificates.pbindH 18, ← TripleCertificates.pbindH 19, ← TripleCertificates.pbindH 21]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 18)
    (TripleCertificates.positiveH 19) (TripleCertificates.positiveH 21) 0 1 (by decide +kernel))
end FullereneGeometry
