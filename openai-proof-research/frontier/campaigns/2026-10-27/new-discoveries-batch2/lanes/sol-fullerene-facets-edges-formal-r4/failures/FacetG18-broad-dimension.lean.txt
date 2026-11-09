import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG18v06 : pG 6 ∈ facetSection qG 18 := by
 refine ⟨(facet_listed_vertices_G 6).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG18v09 : pG 9 ∈ facetSection qG 18 := by
 refine ⟨(facet_listed_vertices_G 9).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG18v10 : pG 10 ∈ facetSection qG 18 := by
 refine ⟨(facet_listed_vertices_G 10).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G18 : affineDimension (facetSection qG 18) = 2 := by
 apply section_dimension_eq qG 18
 · intro hc
   apply not_collinear_of_minor (pG 6) (pG 9) (pG 10) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG18v06 | exact onG18v09 | exact onG18v10)
 · exact ⟨_,onG18v06⟩
end FullereneGeometry
