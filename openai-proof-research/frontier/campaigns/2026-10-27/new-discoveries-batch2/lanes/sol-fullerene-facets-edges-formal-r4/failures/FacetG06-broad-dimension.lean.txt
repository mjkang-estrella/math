import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG06v24 : pG 24 ∈ facetSection qG 6 := by
 refine ⟨(facet_listed_vertices_G 24).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG06v25 : pG 25 ∈ facetSection qG 6 := by
 refine ⟨(facet_listed_vertices_G 25).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG06v28 : pG 28 ∈ facetSection qG 6 := by
 refine ⟨(facet_listed_vertices_G 28).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G06 : affineDimension (facetSection qG 6) = 2 := by
 apply section_dimension_eq qG 6
 · intro hc
   apply not_collinear_of_minor (pG 24) (pG 25) (pG 28) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG06v24 | exact onG06v25 | exact onG06v28)
 · exact ⟨_,onG06v24⟩
end FullereneGeometry
