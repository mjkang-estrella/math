import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH07v12 : pH 12 ∈ facetSection qH 7 := by
 refine ⟨(facet_listed_vertices_H 12).1, ?_⟩
 exact (real_incidence_H 7 12).mp (by decide +kernel)
theorem onH07v13 : pH 13 ∈ facetSection qH 7 := by
 refine ⟨(facet_listed_vertices_H 13).1, ?_⟩
 exact (real_incidence_H 7 13).mp (by decide +kernel)
theorem onH07v17 : pH 17 ∈ facetSection qH 7 := by
 refine ⟨(facet_listed_vertices_H 17).1, ?_⟩
 exact (real_incidence_H 7 17).mp (by decide +kernel)
theorem dimension_H07 : affineDimension (facetSection qH 7) = 2 :=
 section_dimension_eq_of_minor qH 7 (pH 12) (pH 13) (pH 17)
  onH07v12 onH07v13 onH07v17 0 1 (by
   rw [← TripleCertificates.pbindH 12, ← TripleCertificates.pbindH 13, ← TripleCertificates.pbindH 17]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 12)
    (TripleCertificates.positiveH 13) (TripleCertificates.positiveH 17) 0 1 (by decide +kernel))
end FullereneGeometry
