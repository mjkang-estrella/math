import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH00v00 : pH 0 ∈ facetSection qH 0 := by
 refine ⟨(facet_listed_vertices_H 0).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH00v01 : pH 1 ∈ facetSection qH 0 := by
 refine ⟨(facet_listed_vertices_H 1).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH00v02 : pH 2 ∈ facetSection qH 0 := by
 refine ⟨(facet_listed_vertices_H 2).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H00 : affineDimension (facetSection qH 0) = 2 := by
 apply section_dimension_eq qH 0
 · intro hc
   apply not_collinear_of_minor (pH 0) (pH 1) (pH 2) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH00v00 | exact onH00v01 | exact onH00v02)
 · exact ⟨_,onH00v00⟩
end FullereneGeometry
