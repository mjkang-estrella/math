import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG02v22 : pG 22 ∈ facetSection qG 2 := by
 refine ⟨(facet_listed_vertices_G 22).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG02v23 : pG 23 ∈ facetSection qG 2 := by
 refine ⟨(facet_listed_vertices_G 23).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG02v27 : pG 27 ∈ facetSection qG 2 := by
 refine ⟨(facet_listed_vertices_G 27).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G02 : affineDimension (facetSection qG 2) = 2 := by
 apply section_dimension_eq qG 2
 · intro hc
   apply not_collinear_of_minor (pG 22) (pG 23) (pG 27) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG02v22 | exact onG02v23 | exact onG02v27)
 · exact ⟨_,onG02v22⟩
end FullereneGeometry
