import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH25v35 : pH 35 ∈ facetSection qH 25 := by
 refine ⟨(facet_listed_vertices_H 35).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH25v36 : pH 36 ∈ facetSection qH 25 := by
 refine ⟨(facet_listed_vertices_H 36).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH25v38 : pH 38 ∈ facetSection qH 25 := by
 refine ⟨(facet_listed_vertices_H 38).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H25 : affineDimension (facetSection qH 25) = 2 := by
 apply section_dimension_eq qH 25
 · intro hc
   apply not_collinear_of_minor (pH 35) (pH 36) (pH 38) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH25v35 | exact onH25v36 | exact onH25v38)
 · exact ⟨_,onH25v35⟩
end FullereneGeometry
