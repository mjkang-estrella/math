import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG00v00 : pG 0 ∈ facetSection qG 0 := by
 refine ⟨(facet_listed_vertices_G 0).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG00v01 : pG 1 ∈ facetSection qG 0 := by
 refine ⟨(facet_listed_vertices_G 1).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG00v02 : pG 2 ∈ facetSection qG 0 := by
 refine ⟨(facet_listed_vertices_G 2).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G00 : affineDimension (facetSection qG 0) = 2 := by
 apply section_dimension_eq qG 0
 · intro hc
   apply not_collinear_of_minor (pG 0) (pG 1) (pG 2) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG00v00 | exact onG00v01 | exact onG00v02)
 · exact ⟨_,onG00v00⟩
end FullereneGeometry
