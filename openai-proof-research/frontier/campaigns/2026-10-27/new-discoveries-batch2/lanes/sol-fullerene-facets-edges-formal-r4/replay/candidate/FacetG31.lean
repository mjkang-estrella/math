import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG31v15 : pG 15 ∈ facetSection qG 31 := by
 refine ⟨(facet_listed_vertices_G 15).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG31v17 : pG 17 ∈ facetSection qG 31 := by
 refine ⟨(facet_listed_vertices_G 17).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG31v54 : pG 54 ∈ facetSection qG 31 := by
 refine ⟨(facet_listed_vertices_G 54).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G31 : affineDimension (facetSection qG 31) = 2 := by
 apply section_dimension_eq qG 31
 · intro hc
   apply not_collinear_of_minor (pG 15) (pG 17) (pG 54) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG31v15 | exact onG31v17 | exact onG31v54)
 · exact ⟨_,onG31v15⟩
end FullereneGeometry
