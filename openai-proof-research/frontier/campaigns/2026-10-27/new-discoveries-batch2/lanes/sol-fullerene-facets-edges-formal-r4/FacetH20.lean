import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH20v22 : pH 22 ∈ facetSection qH 20 := by
 refine ⟨(facet_listed_vertices_H 22).1, ?_⟩
 exact (real_incidence_H 20 22).mp (by decide +kernel)
theorem onH20v25 : pH 25 ∈ facetSection qH 20 := by
 refine ⟨(facet_listed_vertices_H 25).1, ?_⟩
 exact (real_incidence_H 20 25).mp (by decide +kernel)
theorem onH20v30 : pH 30 ∈ facetSection qH 20 := by
 refine ⟨(facet_listed_vertices_H 30).1, ?_⟩
 exact (real_incidence_H 20 30).mp (by decide +kernel)
theorem dimension_H20 : affineDimension (facetSection qH 20) = 2 :=
 section_dimension_eq_of_minor qH 20 (pH 22) (pH 25) (pH 30)
  onH20v22 onH20v25 onH20v30 0 1 (by
   rw [← TripleCertificates.pbindH 22, ← TripleCertificates.pbindH 25, ← TripleCertificates.pbindH 30]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 22)
    (TripleCertificates.positiveH 25) (TripleCertificates.positiveH 30) 0 1 (by decide +kernel))
end FullereneGeometry
