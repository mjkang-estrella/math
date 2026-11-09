import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG12v00 : pG 0 ∈ facetSection qG 12 := by
 refine ⟨(facet_listed_vertices_G 0).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG12v01 : pG 1 ∈ facetSection qG 12 := by
 refine ⟨(facet_listed_vertices_G 1).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG12v06 : pG 6 ∈ facetSection qG 12 := by
 refine ⟨(facet_listed_vertices_G 6).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G12 : affineDimension (facetSection qG 12) = 2 := by
 apply section_dimension_eq qG 12
 · intro hc
   apply not_collinear_of_minor (pG 0) (pG 1) (pG 6) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG12v00 | exact onG12v01 | exact onG12v06)
 · exact ⟨_,onG12v00⟩
end FullereneGeometry
