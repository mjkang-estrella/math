import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG14v02 : pG 2 ∈ facetSection qG 14 := by
 refine ⟨(facet_listed_vertices_G 2).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG14v03 : pG 3 ∈ facetSection qG 14 := by
 refine ⟨(facet_listed_vertices_G 3).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG14v13 : pG 13 ∈ facetSection qG 14 := by
 refine ⟨(facet_listed_vertices_G 13).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G14 : affineDimension (facetSection qG 14) = 2 := by
 apply section_dimension_eq qG 14
 · intro hc
   apply not_collinear_of_minor (pG 2) (pG 3) (pG 13) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG14v02 | exact onG14v03 | exact onG14v13)
 · exact ⟨_,onG14v02⟩
end FullereneGeometry
