import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG28v44 : pG 44 ∈ facetSection qG 28 := by
 refine ⟨(facet_listed_vertices_G 44).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG28v46 : pG 46 ∈ facetSection qG 28 := by
 refine ⟨(facet_listed_vertices_G 46).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG28v50 : pG 50 ∈ facetSection qG 28 := by
 refine ⟨(facet_listed_vertices_G 50).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G28 : affineDimension (facetSection qG 28) = 2 := by
 apply section_dimension_eq qG 28
 · intro hc
   apply not_collinear_of_minor (pG 44) (pG 46) (pG 50) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG28v44 | exact onG28v46 | exact onG28v50)
 · exact ⟨_,onG28v44⟩
end FullereneGeometry
