import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH11v15 : pH 15 ∈ facetSection qH 11 := by
 refine ⟨(facet_listed_vertices_H 15).1, ?_⟩
 exact (real_incidence_H 11 15).mp (by decide +kernel)
theorem onH11v16 : pH 16 ∈ facetSection qH 11 := by
 refine ⟨(facet_listed_vertices_H 16).1, ?_⟩
 exact (real_incidence_H 11 16).mp (by decide +kernel)
theorem onH11v20 : pH 20 ∈ facetSection qH 11 := by
 refine ⟨(facet_listed_vertices_H 20).1, ?_⟩
 exact (real_incidence_H 11 20).mp (by decide +kernel)
theorem dimension_H11 : affineDimension (facetSection qH 11) = 2 :=
 section_dimension_eq_of_minor qH 11 (pH 15) (pH 16) (pH 20)
  onH11v15 onH11v16 onH11v20 0 1 (by
   rw [← TripleCertificates.pbindH 15, ← TripleCertificates.pbindH 16, ← TripleCertificates.pbindH 20]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 15)
    (TripleCertificates.positiveH 16) (TripleCertificates.positiveH 20) 0 1 (by decide +kernel))
end FullereneGeometry
