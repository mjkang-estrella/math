import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG07v12 : pG 12 ∈ facetSection qG 7 := by
 refine ⟨(facet_listed_vertices_G 12).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG07v13 : pG 13 ∈ facetSection qG 7 := by
 refine ⟨(facet_listed_vertices_G 13).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG07v17 : pG 17 ∈ facetSection qG 7 := by
 refine ⟨(facet_listed_vertices_G 17).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G07 : affineDimension (facetSection qG 7) = 2 := by
 apply section_dimension_eq qG 7
 · intro hc
   apply not_collinear_of_minor (pG 12) (pG 13) (pG 17) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG07v12 | exact onG07v13 | exact onG07v17)
 · exact ⟨_,onG07v12⟩
end FullereneGeometry
