import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG11v15 : pG 15 ∈ facetSection qG 11 := by
 refine ⟨(facet_listed_vertices_G 15).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG11v16 : pG 16 ∈ facetSection qG 11 := by
 refine ⟨(facet_listed_vertices_G 16).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG11v20 : pG 20 ∈ facetSection qG 11 := by
 refine ⟨(facet_listed_vertices_G 20).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G11 : affineDimension (facetSection qG 11) = 2 := by
 apply section_dimension_eq qG 11
 · intro hc
   apply not_collinear_of_minor (pG 15) (pG 16) (pG 20) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG11v15 | exact onG11v16 | exact onG11v20)
 · exact ⟨_,onG11v15⟩
end FullereneGeometry
