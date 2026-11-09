import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH01v00 : pH 0 ∈ facetSection qH 1 := by
 refine ⟨(facet_listed_vertices_H 0).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH01v05 : pH 5 ∈ facetSection qH 1 := by
 refine ⟨(facet_listed_vertices_H 5).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH01v06 : pH 6 ∈ facetSection qH 1 := by
 refine ⟨(facet_listed_vertices_H 6).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H01 : affineDimension (facetSection qH 1) = 2 := by
 apply section_dimension_eq qH 1
 · intro hc
   apply not_collinear_of_minor (pH 0) (pH 5) (pH 6) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH01v00 | exact onH01v05 | exact onH01v06)
 · exact ⟨_,onH01v00⟩
end FullereneGeometry
