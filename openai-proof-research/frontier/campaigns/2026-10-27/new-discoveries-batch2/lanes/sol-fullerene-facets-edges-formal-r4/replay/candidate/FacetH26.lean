import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH26v28 : pH 28 ∈ facetSection qH 26 := by
 refine ⟨(facet_listed_vertices_H 28).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH26v29 : pH 29 ∈ facetSection qH 26 := by
 refine ⟨(facet_listed_vertices_H 29).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH26v42 : pH 42 ∈ facetSection qH 26 := by
 refine ⟨(facet_listed_vertices_H 42).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H26 : affineDimension (facetSection qH 26) = 2 := by
 apply section_dimension_eq qH 26
 · intro hc
   apply not_collinear_of_minor (pH 28) (pH 29) (pH 42) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH26v28 | exact onH26v29 | exact onH26v42)
 · exact ⟨_,onH26v28⟩
end FullereneGeometry
