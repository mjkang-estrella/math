import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG03v29 : pG 29 ∈ facetSection qG 3 := by
 refine ⟨(facet_listed_vertices_G 29).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG03v30 : pG 30 ∈ facetSection qG 3 := by
 refine ⟨(facet_listed_vertices_G 30).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG03v32 : pG 32 ∈ facetSection qG 3 := by
 refine ⟨(facet_listed_vertices_G 32).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G03 : affineDimension (facetSection qG 3) = 2 := by
 apply section_dimension_eq qG 3
 · intro hc
   apply not_collinear_of_minor (pG 29) (pG 30) (pG 32) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG03v29 | exact onG03v30 | exact onG03v32)
 · exact ⟨_,onG03v29⟩
end FullereneGeometry
