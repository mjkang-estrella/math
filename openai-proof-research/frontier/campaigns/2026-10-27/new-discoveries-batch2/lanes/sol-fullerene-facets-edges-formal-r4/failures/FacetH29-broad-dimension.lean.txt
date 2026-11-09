import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH29v12 : pH 12 ∈ facetSection qH 29 := by
 refine ⟨(facet_listed_vertices_H 12).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH29v14 : pH 14 ∈ facetSection qH 29 := by
 refine ⟨(facet_listed_vertices_H 14).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH29v40 : pH 40 ∈ facetSection qH 29 := by
 refine ⟨(facet_listed_vertices_H 40).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H29 : affineDimension (facetSection qH 29) = 2 := by
 apply section_dimension_eq qH 29
 · intro hc
   apply not_collinear_of_minor (pH 12) (pH 14) (pH 40) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH29v12 | exact onH29v14 | exact onH29v40)
 · exact ⟨_,onH29v12⟩
end FullereneGeometry
