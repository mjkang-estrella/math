import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG30v47 : pG 47 ∈ facetSection qG 30 := by
 refine ⟨(facet_listed_vertices_G 47).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG30v48 : pG 48 ∈ facetSection qG 30 := by
 refine ⟨(facet_listed_vertices_G 48).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG30v56 : pG 56 ∈ facetSection qG 30 := by
 refine ⟨(facet_listed_vertices_G 56).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G30 : affineDimension (facetSection qG 30) = 2 := by
 apply section_dimension_eq qG 30
 · intro hc
   apply not_collinear_of_minor (pG 47) (pG 48) (pG 56) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG30v47 | exact onG30v48 | exact onG30v56)
 · exact ⟨_,onG30v47⟩
end FullereneGeometry
