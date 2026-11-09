import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG01v00 : pG 0 ∈ facetSection qG 1 := by
 refine ⟨(facet_listed_vertices_G 0).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG01v05 : pG 5 ∈ facetSection qG 1 := by
 refine ⟨(facet_listed_vertices_G 5).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG01v06 : pG 6 ∈ facetSection qG 1 := by
 refine ⟨(facet_listed_vertices_G 6).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G01 : affineDimension (facetSection qG 1) = 2 := by
 apply section_dimension_eq qG 1
 · intro hc
   apply not_collinear_of_minor (pG 0) (pG 5) (pG 6) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG01v00 | exact onG01v05 | exact onG01v06)
 · exact ⟨_,onG01v00⟩
end FullereneGeometry
