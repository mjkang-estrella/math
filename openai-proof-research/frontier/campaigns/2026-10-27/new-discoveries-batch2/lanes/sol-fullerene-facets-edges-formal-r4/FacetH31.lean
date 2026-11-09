import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH31v15 : pH 15 ∈ facetSection qH 31 := by
 refine ⟨(facet_listed_vertices_H 15).1, ?_⟩
 exact (real_incidence_H 31 15).mp (by decide +kernel)
theorem onH31v17 : pH 17 ∈ facetSection qH 31 := by
 refine ⟨(facet_listed_vertices_H 17).1, ?_⟩
 exact (real_incidence_H 31 17).mp (by decide +kernel)
theorem onH31v54 : pH 54 ∈ facetSection qH 31 := by
 refine ⟨(facet_listed_vertices_H 54).1, ?_⟩
 exact (real_incidence_H 31 54).mp (by decide +kernel)
theorem dimension_H31 : affineDimension (facetSection qH 31) = 2 :=
 section_dimension_eq_of_minor qH 31 (pH 15) (pH 17) (pH 54)
  onH31v15 onH31v17 onH31v54 0 1 (by
   rw [← TripleCertificates.pbindH 15, ← TripleCertificates.pbindH 17, ← TripleCertificates.pbindH 54]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 15)
    (TripleCertificates.positiveH 17) (TripleCertificates.positiveH 54) 0 1 (by decide +kernel))
end FullereneGeometry
