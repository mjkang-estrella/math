import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH23v33 : pH 33 ∈ facetSection qH 23 := by
 refine ⟨(facet_listed_vertices_H 33).1, ?_⟩
 exact (real_incidence_H 23 33).mp (by decide +kernel)
theorem onH23v34 : pH 34 ∈ facetSection qH 23 := by
 refine ⟨(facet_listed_vertices_H 34).1, ?_⟩
 exact (real_incidence_H 23 34).mp (by decide +kernel)
theorem onH23v37 : pH 37 ∈ facetSection qH 23 := by
 refine ⟨(facet_listed_vertices_H 37).1, ?_⟩
 exact (real_incidence_H 23 37).mp (by decide +kernel)
theorem dimension_H23 : affineDimension (facetSection qH 23) = 2 :=
 section_dimension_eq_of_minor qH 23 (pH 33) (pH 34) (pH 37)
  onH23v33 onH23v34 onH23v37 0 1 (by
   rw [← TripleCertificates.pbindH 33, ← TripleCertificates.pbindH 34, ← TripleCertificates.pbindH 37]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 33)
    (TripleCertificates.positiveH 34) (TripleCertificates.positiveH 37) 0 1 (by decide +kernel))
end FullereneGeometry
