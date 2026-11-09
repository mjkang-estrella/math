import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH29v12 : pH 12 ∈ facetSection qH 29 := by
 refine ⟨(facet_listed_vertices_H 12).1, ?_⟩
 exact (real_incidence_H 29 12).mp (by decide +kernel)
theorem onH29v14 : pH 14 ∈ facetSection qH 29 := by
 refine ⟨(facet_listed_vertices_H 14).1, ?_⟩
 exact (real_incidence_H 29 14).mp (by decide +kernel)
theorem onH29v40 : pH 40 ∈ facetSection qH 29 := by
 refine ⟨(facet_listed_vertices_H 40).1, ?_⟩
 exact (real_incidence_H 29 40).mp (by decide +kernel)
theorem dimension_H29 : affineDimension (facetSection qH 29) = 2 :=
 section_dimension_eq_of_minor qH 29 (pH 12) (pH 14) (pH 40)
  onH29v12 onH29v14 onH29v40 0 1 (by
   rw [← TripleCertificates.pbindH 12, ← TripleCertificates.pbindH 14, ← TripleCertificates.pbindH 40]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 12)
    (TripleCertificates.positiveH 14) (TripleCertificates.positiveH 40) 0 1 (by decide +kernel))
end FullereneGeometry
