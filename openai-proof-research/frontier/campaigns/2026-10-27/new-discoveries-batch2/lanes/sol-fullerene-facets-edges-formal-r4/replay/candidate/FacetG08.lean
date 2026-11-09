import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG08v10 : pG 10 ∈ facetSection qG 8 := by
 refine ⟨(facet_listed_vertices_G 10).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG08v11 : pG 11 ∈ facetSection qG 8 := by
 refine ⟨(facet_listed_vertices_G 11).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG08v14 : pG 14 ∈ facetSection qG 8 := by
 refine ⟨(facet_listed_vertices_G 14).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G08 : affineDimension (facetSection qG 8) = 2 := by
 apply section_dimension_eq qG 8
 · intro hc
   apply not_collinear_of_minor (pG 10) (pG 11) (pG 14) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG08v10 | exact onG08v11 | exact onG08v14)
 · exact ⟨_,onG08v10⟩
end FullereneGeometry
