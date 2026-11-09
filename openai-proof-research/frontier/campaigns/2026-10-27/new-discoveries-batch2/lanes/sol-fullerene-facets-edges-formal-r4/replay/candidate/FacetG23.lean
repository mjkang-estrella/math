import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG23v32 : pG 32 ∈ facetSection qG 23 := by
 refine ⟨(facet_listed_vertices_G 32).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG23v33 : pG 33 ∈ facetSection qG 23 := by
 refine ⟨(facet_listed_vertices_G 33).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG23v36 : pG 36 ∈ facetSection qG 23 := by
 refine ⟨(facet_listed_vertices_G 36).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G23 : affineDimension (facetSection qG 23) = 2 := by
 apply section_dimension_eq qG 23
 · intro hc
   apply not_collinear_of_minor (pG 32) (pG 33) (pG 36) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG23v32 | exact onG23v33 | exact onG23v36)
 · exact ⟨_,onG23v32⟩
end FullereneGeometry
