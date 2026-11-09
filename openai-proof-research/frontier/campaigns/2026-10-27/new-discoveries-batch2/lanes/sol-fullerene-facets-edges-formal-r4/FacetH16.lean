import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH16v04 : pH 4 ∈ facetSection qH 16 := by
 refine ⟨(facet_listed_vertices_H 4).1, ?_⟩
 exact (real_incidence_H 16 4).mp (by decide +kernel)
theorem onH16v05 : pH 5 ∈ facetSection qH 16 := by
 refine ⟨(facet_listed_vertices_H 5).1, ?_⟩
 exact (real_incidence_H 16 5).mp (by decide +kernel)
theorem onH16v07 : pH 7 ∈ facetSection qH 16 := by
 refine ⟨(facet_listed_vertices_H 7).1, ?_⟩
 exact (real_incidence_H 16 7).mp (by decide +kernel)
theorem dimension_H16 : affineDimension (facetSection qH 16) = 2 :=
 section_dimension_eq_of_minor qH 16 (pH 4) (pH 5) (pH 7)
  onH16v04 onH16v05 onH16v07 0 1 (by
   rw [← TripleCertificates.pbindH 4, ← TripleCertificates.pbindH 5, ← TripleCertificates.pbindH 7]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 4)
    (TripleCertificates.positiveH 5) (TripleCertificates.positiveH 7) 0 1 (by decide +kernel))
end FullereneGeometry
