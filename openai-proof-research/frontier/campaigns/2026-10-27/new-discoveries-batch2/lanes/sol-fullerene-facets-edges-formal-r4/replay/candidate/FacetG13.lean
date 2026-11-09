import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG13v01 : pG 1 ∈ facetSection qG 13 := by
 refine ⟨(facet_listed_vertices_G 1).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG13v02 : pG 2 ∈ facetSection qG 13 := by
 refine ⟨(facet_listed_vertices_G 2).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG13v11 : pG 11 ∈ facetSection qG 13 := by
 refine ⟨(facet_listed_vertices_G 11).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G13 : affineDimension (facetSection qG 13) = 2 := by
 apply section_dimension_eq qG 13
 · intro hc
   apply not_collinear_of_minor (pG 1) (pG 2) (pG 11) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG13v01 | exact onG13v02 | exact onG13v11)
 · exact ⟨_,onG13v01⟩
end FullereneGeometry
