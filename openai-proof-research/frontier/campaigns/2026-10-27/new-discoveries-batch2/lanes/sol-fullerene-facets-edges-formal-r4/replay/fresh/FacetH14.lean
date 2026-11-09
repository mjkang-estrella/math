import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH14v02 : pH 2 ∈ facetSection qH 14 := by
 refine ⟨(facet_listed_vertices_H 2).1, ?_⟩
 exact (real_incidence_H 14 2).mp (by decide +kernel)
theorem onH14v03 : pH 3 ∈ facetSection qH 14 := by
 refine ⟨(facet_listed_vertices_H 3).1, ?_⟩
 exact (real_incidence_H 14 3).mp (by decide +kernel)
theorem onH14v13 : pH 13 ∈ facetSection qH 14 := by
 refine ⟨(facet_listed_vertices_H 13).1, ?_⟩
 exact (real_incidence_H 14 13).mp (by decide +kernel)
theorem dimension_H14 : affineDimension (facetSection qH 14) = 2 :=
 section_dimension_eq_of_minor qH 14 (pH 2) (pH 3) (pH 13)
  onH14v02 onH14v03 onH14v13 0 1 (by
   rw [← TripleCertificates.pbindH 2, ← TripleCertificates.pbindH 3, ← TripleCertificates.pbindH 13]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 2)
    (TripleCertificates.positiveH 3) (TripleCertificates.positiveH 13) 0 1 (by decide +kernel))
end FullereneGeometry
