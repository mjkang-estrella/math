import FeasibleH
import IncidenceRealH
import FacetDimension
import MinorCore
noncomputable section
namespace FullereneGeometry
theorem onH25v35 : pH 35 ∈ facetSection qH 25 := by
 refine ⟨(facet_listed_vertices_H 35).1, ?_⟩
 exact (real_incidence_H 25 35).mp (by decide +kernel)
theorem onH25v36 : pH 36 ∈ facetSection qH 25 := by
 refine ⟨(facet_listed_vertices_H 36).1, ?_⟩
 exact (real_incidence_H 25 36).mp (by decide +kernel)
theorem onH25v38 : pH 38 ∈ facetSection qH 25 := by
 refine ⟨(facet_listed_vertices_H 38).1, ?_⟩
 exact (real_incidence_H 25 38).mp (by decide +kernel)
theorem dimension_H25 : affineDimension (facetSection qH 25) = 2 :=
 section_dimension_eq_of_minor qH 25 (pH 35) (pH 36) (pH 38)
  onH25v35 onH25v36 onH25v38 0 1 (by
   rw [← TripleCertificates.pbindH 35, ← TripleCertificates.pbindH 36, ← TripleCertificates.pbindH 38]
   exact TripleCertificates.minor_real _ _ _ (TripleCertificates.positiveH 35)
    (TripleCertificates.positiveH 36) (TripleCertificates.positiveH 38) 0 1 (by decide +kernel))
end FullereneGeometry
