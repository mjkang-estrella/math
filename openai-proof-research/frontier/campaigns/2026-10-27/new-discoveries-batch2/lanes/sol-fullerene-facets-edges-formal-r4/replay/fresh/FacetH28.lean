import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH28v45 : pH 45 ∈ facetSection qH 28 := by
 refine ⟨(facet_listed_vertices_H 45).1, ?_⟩
 exact (real_incidence_H 28 45).mp (by decide +kernel)
theorem onH28v47 : pH 47 ∈ facetSection qH 28 := by
 refine ⟨(facet_listed_vertices_H 47).1, ?_⟩
 exact (real_incidence_H 28 47).mp (by decide +kernel)
theorem onH28v51 : pH 51 ∈ facetSection qH 28 := by
 refine ⟨(facet_listed_vertices_H 51).1, ?_⟩
 exact (real_incidence_H 28 51).mp (by decide +kernel)
theorem dimension_H28 : affineDimension (facetSection qH 28) = 2 :=
 section_dimension_eq_of_minor qH 28 (pH 45) (pH 47) (pH 51)
  onH28v45 onH28v47 onH28v51 0 1 (by
   rw [← TripleCertificates.pbindH 45, ← TripleCertificates.pbindH 47, ← TripleCertificates.pbindH 51]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 45)
    (TripleCertificates.positiveH 47) (TripleCertificates.positiveH 51) 0 1 (by decide +kernel))
end FullereneGeometry
