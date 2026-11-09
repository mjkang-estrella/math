import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG26v41 : pG 41 ∈ facetSection qG 26 := by
 refine ⟨(facet_listed_vertices_G 41).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG26v43 : pG 43 ∈ facetSection qG 26 := by
 refine ⟨(facet_listed_vertices_G 43).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG26v49 : pG 49 ∈ facetSection qG 26 := by
 refine ⟨(facet_listed_vertices_G 49).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G26 : affineDimension (facetSection qG 26) = 2 := by
 apply section_dimension_eq qG 26
 · intro hc
   apply not_collinear_of_minor (pG 41) (pG 43) (pG 49) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG26v41 | exact onG26v43 | exact onG26v49)
 · exact ⟨_,onG26v41⟩
end FullereneGeometry
