import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH07v12 : pH 12 ∈ facetSection qH 7 := by
 refine ⟨(facet_listed_vertices_H 12).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH07v13 : pH 13 ∈ facetSection qH 7 := by
 refine ⟨(facet_listed_vertices_H 13).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH07v17 : pH 17 ∈ facetSection qH 7 := by
 refine ⟨(facet_listed_vertices_H 17).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H07 : affineDimension (facetSection qH 7) = 2 := by
 apply section_dimension_eq qH 7
 · intro hc
   apply not_collinear_of_minor (pH 12) (pH 13) (pH 17) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH07v12 | exact onH07v13 | exact onH07v17)
 · exact ⟨_,onH07v12⟩
end FullereneGeometry
