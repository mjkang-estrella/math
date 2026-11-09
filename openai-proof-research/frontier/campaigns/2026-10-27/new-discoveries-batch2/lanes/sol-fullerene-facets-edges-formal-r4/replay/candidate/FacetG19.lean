import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG19v07 : pG 7 ∈ facetSection qG 19 := by
 refine ⟨(facet_listed_vertices_G 7).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG19v08 : pG 8 ∈ facetSection qG 19 := by
 refine ⟨(facet_listed_vertices_G 8).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG19v21 : pG 21 ∈ facetSection qG 19 := by
 refine ⟨(facet_listed_vertices_G 21).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G19 : affineDimension (facetSection qG 19) = 2 := by
 apply section_dimension_eq qG 19
 · intro hc
   apply not_collinear_of_minor (pG 7) (pG 8) (pG 21) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG19v07 | exact onG19v08 | exact onG19v21)
 · exact ⟨_,onG19v07⟩
end FullereneGeometry
