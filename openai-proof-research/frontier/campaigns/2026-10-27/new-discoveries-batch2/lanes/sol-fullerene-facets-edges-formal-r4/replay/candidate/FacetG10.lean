import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG10v44 : pG 44 ∈ facetSection qG 10 := by
 refine ⟨(facet_listed_vertices_G 44).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG10v45 : pG 45 ∈ facetSection qG 10 := by
 refine ⟨(facet_listed_vertices_G 45).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG10v48 : pG 48 ∈ facetSection qG 10 := by
 refine ⟨(facet_listed_vertices_G 48).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G10 : affineDimension (facetSection qG 10) = 2 := by
 apply section_dimension_eq qG 10
 · intro hc
   apply not_collinear_of_minor (pG 44) (pG 45) (pG 48) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG10v44 | exact onG10v45 | exact onG10v48)
 · exact ⟨_,onG10v44⟩
end FullereneGeometry
