import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG27v18 : pG 18 ∈ facetSection qG 27 := by
 refine ⟨(facet_listed_vertices_G 18).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG27v20 : pG 20 ∈ facetSection qG 27 := by
 refine ⟨(facet_listed_vertices_G 20).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG27v49 : pG 49 ∈ facetSection qG 27 := by
 refine ⟨(facet_listed_vertices_G 49).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G27 : affineDimension (facetSection qG 27) = 2 := by
 apply section_dimension_eq qG 27
 · intro hc
   apply not_collinear_of_minor (pG 18) (pG 20) (pG 49) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG27v18 | exact onG27v20 | exact onG27v49)
 · exact ⟨_,onG27v18⟩
end FullereneGeometry
