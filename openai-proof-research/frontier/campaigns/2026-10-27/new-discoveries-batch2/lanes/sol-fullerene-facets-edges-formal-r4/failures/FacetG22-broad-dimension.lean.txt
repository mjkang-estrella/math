import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG22v26 : pG 26 ∈ facetSection qG 22 := by
 refine ⟨(facet_listed_vertices_G 26).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG22v27 : pG 27 ∈ facetSection qG 22 := by
 refine ⟨(facet_listed_vertices_G 27).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG22v31 : pG 31 ∈ facetSection qG 22 := by
 refine ⟨(facet_listed_vertices_G 31).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G22 : affineDimension (facetSection qG 22) = 2 := by
 apply section_dimension_eq qG 22
 · intro hc
   apply not_collinear_of_minor (pG 26) (pG 27) (pG 31) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG22v26 | exact onG22v27 | exact onG22v31)
 · exact ⟨_,onG22v26⟩
end FullereneGeometry
