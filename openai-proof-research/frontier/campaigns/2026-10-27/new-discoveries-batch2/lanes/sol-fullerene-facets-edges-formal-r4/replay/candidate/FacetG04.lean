import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG04v41 : pG 41 ∈ facetSection qG 4 := by
 refine ⟨(facet_listed_vertices_G 41).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG04v42 : pG 42 ∈ facetSection qG 4 := by
 refine ⟨(facet_listed_vertices_G 42).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG04v46 : pG 46 ∈ facetSection qG 4 := by
 refine ⟨(facet_listed_vertices_G 46).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G04 : affineDimension (facetSection qG 4) = 2 := by
 apply section_dimension_eq qG 4
 · intro hc
   apply not_collinear_of_minor (pG 41) (pG 42) (pG 46) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG04v41 | exact onG04v42 | exact onG04v46)
 · exact ⟨_,onG04v41⟩
end FullereneGeometry
