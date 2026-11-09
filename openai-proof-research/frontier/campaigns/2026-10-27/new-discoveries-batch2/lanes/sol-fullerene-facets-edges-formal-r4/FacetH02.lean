import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH02v22 : pH 22 ∈ facetSection qH 2 := by
 refine ⟨(facet_listed_vertices_H 22).1, ?_⟩
 exact (real_incidence_H 2 22).mp (by decide +kernel)
theorem onH02v23 : pH 23 ∈ facetSection qH 2 := by
 refine ⟨(facet_listed_vertices_H 23).1, ?_⟩
 exact (real_incidence_H 2 23).mp (by decide +kernel)
theorem onH02v27 : pH 27 ∈ facetSection qH 2 := by
 refine ⟨(facet_listed_vertices_H 27).1, ?_⟩
 exact (real_incidence_H 2 27).mp (by decide +kernel)
theorem dimension_H02 : affineDimension (facetSection qH 2) = 2 :=
 section_dimension_eq_of_minor qH 2 (pH 22) (pH 23) (pH 27)
  onH02v22 onH02v23 onH02v27 0 1 (by
   rw [← TripleCertificates.pbindH 22, ← TripleCertificates.pbindH 23, ← TripleCertificates.pbindH 27]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 22)
    (TripleCertificates.positiveH 23) (TripleCertificates.positiveH 27) 0 1 (by decide +kernel))
end FullereneGeometry
