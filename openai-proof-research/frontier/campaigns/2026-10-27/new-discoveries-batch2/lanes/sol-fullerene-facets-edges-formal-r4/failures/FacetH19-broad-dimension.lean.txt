import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH19v07 : pH 7 ∈ facetSection qH 19 := by
 refine ⟨(facet_listed_vertices_H 7).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH19v08 : pH 8 ∈ facetSection qH 19 := by
 refine ⟨(facet_listed_vertices_H 8).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH19v21 : pH 21 ∈ facetSection qH 19 := by
 refine ⟨(facet_listed_vertices_H 21).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H19 : affineDimension (facetSection qH 19) = 2 := by
 apply section_dimension_eq qH 19
 · intro hc
   apply not_collinear_of_minor (pH 7) (pH 8) (pH 21) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH19v07 | exact onH19v08 | exact onH19v21)
 · exact ⟨_,onH19v07⟩
end FullereneGeometry
