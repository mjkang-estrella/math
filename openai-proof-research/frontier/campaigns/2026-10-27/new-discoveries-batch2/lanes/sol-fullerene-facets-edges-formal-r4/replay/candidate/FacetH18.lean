import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH18v06 : pH 6 ∈ facetSection qH 18 := by
 refine ⟨(facet_listed_vertices_H 6).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH18v09 : pH 9 ∈ facetSection qH 18 := by
 refine ⟨(facet_listed_vertices_H 9).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH18v10 : pH 10 ∈ facetSection qH 18 := by
 refine ⟨(facet_listed_vertices_H 10).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H18 : affineDimension (facetSection qH 18) = 2 := by
 apply section_dimension_eq qH 18
 · intro hc
   apply not_collinear_of_minor (pH 6) (pH 9) (pH 10) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH18v06 | exact onH18v09 | exact onH18v10)
 · exact ⟨_,onH18v06⟩
end FullereneGeometry
