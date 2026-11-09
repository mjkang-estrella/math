import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH17v08 : pH 8 ∈ facetSection qH 17 := by
 refine ⟨(facet_listed_vertices_H 8).1, ?_⟩
 exact (real_incidence_H 17 8).mp (by decide +kernel)
theorem onH17v09 : pH 9 ∈ facetSection qH 17 := by
 refine ⟨(facet_listed_vertices_H 9).1, ?_⟩
 exact (real_incidence_H 17 9).mp (by decide +kernel)
theorem onH17v22 : pH 22 ∈ facetSection qH 17 := by
 refine ⟨(facet_listed_vertices_H 22).1, ?_⟩
 exact (real_incidence_H 17 22).mp (by decide +kernel)
theorem dimension_H17 : affineDimension (facetSection qH 17) = 2 :=
 section_dimension_eq_of_minor qH 17 (pH 8) (pH 9) (pH 22)
  onH17v08 onH17v09 onH17v22 0 1 (by
   rw [← TripleCertificates.pbindH 8, ← TripleCertificates.pbindH 9, ← TripleCertificates.pbindH 22]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 8)
    (TripleCertificates.positiveH 9) (TripleCertificates.positiveH 22) 0 1 (by decide +kernel))
end FullereneGeometry
