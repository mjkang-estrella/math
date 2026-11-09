import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH13v01 : pH 1 ∈ facetSection qH 13 := by
 refine ⟨(facet_listed_vertices_H 1).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH13v02 : pH 2 ∈ facetSection qH 13 := by
 refine ⟨(facet_listed_vertices_H 2).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH13v11 : pH 11 ∈ facetSection qH 13 := by
 refine ⟨(facet_listed_vertices_H 11).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H13 : affineDimension (facetSection qH 13) = 2 := by
 apply section_dimension_eq qH 13
 · intro hc
   apply not_collinear_of_minor (pH 1) (pH 2) (pH 11) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH13v01 | exact onH13v02 | exact onH13v11)
 · exact ⟨_,onH13v01⟩
end FullereneGeometry
