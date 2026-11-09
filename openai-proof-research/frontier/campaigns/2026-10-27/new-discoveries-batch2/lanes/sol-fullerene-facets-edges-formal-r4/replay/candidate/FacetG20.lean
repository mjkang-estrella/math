import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG20v22 : pG 22 ∈ facetSection qG 20 := by
 refine ⟨(facet_listed_vertices_G 22).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG20v25 : pG 25 ∈ facetSection qG 20 := by
 refine ⟨(facet_listed_vertices_G 25).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG20v29 : pG 29 ∈ facetSection qG 20 := by
 refine ⟨(facet_listed_vertices_G 29).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G20 : affineDimension (facetSection qG 20) = 2 := by
 apply section_dimension_eq qG 20
 · intro hc
   apply not_collinear_of_minor (pG 22) (pG 25) (pG 29) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG20v22 | exact onG20v25 | exact onG20v29)
 · exact ⟨_,onG20v22⟩
end FullereneGeometry
