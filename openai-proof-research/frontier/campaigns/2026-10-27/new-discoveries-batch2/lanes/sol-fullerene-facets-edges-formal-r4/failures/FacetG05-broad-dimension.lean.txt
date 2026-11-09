import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG05v18 : pG 18 ∈ facetSection qG 5 := by
 refine ⟨(facet_listed_vertices_G 18).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG05v19 : pG 19 ∈ facetSection qG 5 := by
 refine ⟨(facet_listed_vertices_G 19).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG05v21 : pG 21 ∈ facetSection qG 5 := by
 refine ⟨(facet_listed_vertices_G 21).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G05 : affineDimension (facetSection qG 5) = 2 := by
 apply section_dimension_eq qG 5
 · intro hc
   apply not_collinear_of_minor (pG 18) (pG 19) (pG 21) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG05v18 | exact onG05v19 | exact onG05v21)
 · exact ⟨_,onG05v18⟩
end FullereneGeometry
