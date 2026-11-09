import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG25v34 : pG 34 ∈ facetSection qG 25 := by
 refine ⟨(facet_listed_vertices_G 34).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG25v35 : pG 35 ∈ facetSection qG 25 := by
 refine ⟨(facet_listed_vertices_G 35).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG25v37 : pG 37 ∈ facetSection qG 25 := by
 refine ⟨(facet_listed_vertices_G 37).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G25 : affineDimension (facetSection qG 25) = 2 := by
 apply section_dimension_eq qG 25
 · intro hc
   apply not_collinear_of_minor (pG 34) (pG 35) (pG 37) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG25v34 | exact onG25v35 | exact onG25v37)
 · exact ⟨_,onG25v34⟩
end FullereneGeometry
