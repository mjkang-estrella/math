import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG16v04 : pG 4 ∈ facetSection qG 16 := by
 refine ⟨(facet_listed_vertices_G 4).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG16v05 : pG 5 ∈ facetSection qG 16 := by
 refine ⟨(facet_listed_vertices_G 5).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG16v07 : pG 7 ∈ facetSection qG 16 := by
 refine ⟨(facet_listed_vertices_G 7).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G16 : affineDimension (facetSection qG 16) = 2 := by
 apply section_dimension_eq qG 16
 · intro hc
   apply not_collinear_of_minor (pG 4) (pG 5) (pG 7) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG16v04 | exact onG16v05 | exact onG16v07)
 · exact ⟨_,onG16v04⟩
end FullereneGeometry
