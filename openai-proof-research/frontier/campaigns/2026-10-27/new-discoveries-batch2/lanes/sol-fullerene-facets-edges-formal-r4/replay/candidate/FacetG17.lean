import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG17v08 : pG 8 ∈ facetSection qG 17 := by
 refine ⟨(facet_listed_vertices_G 8).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG17v09 : pG 9 ∈ facetSection qG 17 := by
 refine ⟨(facet_listed_vertices_G 9).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG17v22 : pG 22 ∈ facetSection qG 17 := by
 refine ⟨(facet_listed_vertices_G 22).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G17 : affineDimension (facetSection qG 17) = 2 := by
 apply section_dimension_eq qG 17
 · intro hc
   apply not_collinear_of_minor (pG 8) (pG 9) (pG 22) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG17v08 | exact onG17v09 | exact onG17v22)
 · exact ⟨_,onG17v08⟩
end FullereneGeometry
