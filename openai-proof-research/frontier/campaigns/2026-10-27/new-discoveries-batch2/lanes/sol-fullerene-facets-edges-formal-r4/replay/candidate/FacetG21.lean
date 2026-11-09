import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG21v30 : pG 30 ∈ facetSection qG 21 := by
 refine ⟨(facet_listed_vertices_G 30).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG21v31 : pG 31 ∈ facetSection qG 21 := by
 refine ⟨(facet_listed_vertices_G 31).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG21v35 : pG 35 ∈ facetSection qG 21 := by
 refine ⟨(facet_listed_vertices_G 35).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G21 : affineDimension (facetSection qG 21) = 2 := by
 apply section_dimension_eq qG 21
 · intro hc
   apply not_collinear_of_minor (pG 30) (pG 31) (pG 35) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG21v30 | exact onG21v31 | exact onG21v35)
 · exact ⟨_,onG21v30⟩
end FullereneGeometry
