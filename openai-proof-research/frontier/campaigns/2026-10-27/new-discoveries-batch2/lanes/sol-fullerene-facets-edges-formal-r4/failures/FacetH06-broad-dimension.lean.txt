import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH06v24 : pH 24 ∈ facetSection qH 6 := by
 refine ⟨(facet_listed_vertices_H 24).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH06v25 : pH 25 ∈ facetSection qH 6 := by
 refine ⟨(facet_listed_vertices_H 25).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH06v29 : pH 29 ∈ facetSection qH 6 := by
 refine ⟨(facet_listed_vertices_H 29).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H06 : affineDimension (facetSection qH 6) = 2 := by
 apply section_dimension_eq qH 6
 · intro hc
   apply not_collinear_of_minor (pH 24) (pH 25) (pH 29) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH06v24 | exact onH06v25 | exact onH06v29)
 · exact ⟨_,onH06v24⟩
end FullereneGeometry
