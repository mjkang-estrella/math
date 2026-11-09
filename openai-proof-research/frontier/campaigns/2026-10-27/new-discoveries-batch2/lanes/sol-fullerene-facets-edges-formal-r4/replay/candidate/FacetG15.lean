import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG15v03 : pG 3 ∈ facetSection qG 15 := by
 refine ⟨(facet_listed_vertices_G 3).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG15v04 : pG 4 ∈ facetSection qG 15 := by
 refine ⟨(facet_listed_vertices_G 4).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG15v16 : pG 16 ∈ facetSection qG 15 := by
 refine ⟨(facet_listed_vertices_G 16).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G15 : affineDimension (facetSection qG 15) = 2 := by
 apply section_dimension_eq qG 15
 · intro hc
   apply not_collinear_of_minor (pG 3) (pG 4) (pG 16) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG15v03 | exact onG15v04 | exact onG15v16)
 · exact ⟨_,onG15v03⟩
end FullereneGeometry
