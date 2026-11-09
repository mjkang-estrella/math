import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH09v38 : pH 38 ∈ facetSection qH 9 := by
 refine ⟨(facet_listed_vertices_H 38).1, ?_⟩
 exact (real_incidence_H 9 38).mp (by decide +kernel)
theorem onH09v39 : pH 39 ∈ facetSection qH 9 := by
 refine ⟨(facet_listed_vertices_H 39).1, ?_⟩
 exact (real_incidence_H 9 39).mp (by decide +kernel)
theorem onH09v41 : pH 41 ∈ facetSection qH 9 := by
 refine ⟨(facet_listed_vertices_H 41).1, ?_⟩
 exact (real_incidence_H 9 41).mp (by decide +kernel)
theorem dimension_H09 : affineDimension (facetSection qH 9) = 2 :=
 section_dimension_eq_of_minor qH 9 (pH 38) (pH 39) (pH 41)
  onH09v38 onH09v39 onH09v41 0 1 (by
   rw [← TripleCertificates.pbindH 38, ← TripleCertificates.pbindH 39, ← TripleCertificates.pbindH 41]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 38)
    (TripleCertificates.positiveH 39) (TripleCertificates.positiveH 41) 0 1 (by decide +kernel))
end FullereneGeometry
