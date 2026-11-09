import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH04v42 : pH 42 ∈ facetSection qH 4 := by
 refine ⟨(facet_listed_vertices_H 42).1, ?_⟩
 exact (real_incidence_H 4 42).mp (by decide +kernel)
theorem onH04v43 : pH 43 ∈ facetSection qH 4 := by
 refine ⟨(facet_listed_vertices_H 43).1, ?_⟩
 exact (real_incidence_H 4 43).mp (by decide +kernel)
theorem onH04v47 : pH 47 ∈ facetSection qH 4 := by
 refine ⟨(facet_listed_vertices_H 47).1, ?_⟩
 exact (real_incidence_H 4 47).mp (by decide +kernel)
theorem dimension_H04 : affineDimension (facetSection qH 4) = 2 :=
 section_dimension_eq_of_minor qH 4 (pH 42) (pH 43) (pH 47)
  onH04v42 onH04v43 onH04v47 0 1 (by
   rw [← TripleCertificates.pbindH 42, ← TripleCertificates.pbindH 43, ← TripleCertificates.pbindH 47]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 42)
    (TripleCertificates.positiveH 43) (TripleCertificates.positiveH 47) 0 1 (by decide +kernel))
end FullereneGeometry
