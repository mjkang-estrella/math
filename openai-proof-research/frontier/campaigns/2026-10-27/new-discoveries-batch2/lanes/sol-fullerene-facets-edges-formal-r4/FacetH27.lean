import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH27v18 : pH 18 ∈ facetSection qH 27 := by
 refine ⟨(facet_listed_vertices_H 18).1, ?_⟩
 exact (real_incidence_H 27 18).mp (by decide +kernel)
theorem onH27v20 : pH 20 ∈ facetSection qH 27 := by
 refine ⟨(facet_listed_vertices_H 20).1, ?_⟩
 exact (real_incidence_H 27 20).mp (by decide +kernel)
theorem onH27v50 : pH 50 ∈ facetSection qH 27 := by
 refine ⟨(facet_listed_vertices_H 50).1, ?_⟩
 exact (real_incidence_H 27 50).mp (by decide +kernel)
theorem dimension_H27 : affineDimension (facetSection qH 27) = 2 :=
 section_dimension_eq_of_minor qH 27 (pH 18) (pH 20) (pH 50)
  onH27v18 onH27v20 onH27v50 0 1 (by
   rw [← TripleCertificates.pbindH 18, ← TripleCertificates.pbindH 20, ← TripleCertificates.pbindH 50]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 18)
    (TripleCertificates.positiveH 20) (TripleCertificates.positiveH 50) 0 1 (by decide +kernel))
end FullereneGeometry
