import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG29v12 : pG 12 ∈ facetSection qG 29 := by
 refine ⟨(facet_listed_vertices_G 12).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG29v14 : pG 14 ∈ facetSection qG 29 := by
 refine ⟨(facet_listed_vertices_G 14).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG29v39 : pG 39 ∈ facetSection qG 29 := by
 refine ⟨(facet_listed_vertices_G 39).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G29 : affineDimension (facetSection qG 29) = 2 := by
 apply section_dimension_eq qG 29
 · intro hc
   apply not_collinear_of_minor (pG 12) (pG 14) (pG 39) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG29v12 | exact onG29v14 | exact onG29v39)
 · exact ⟨_,onG29v12⟩
end FullereneGeometry
