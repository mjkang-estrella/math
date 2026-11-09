import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG24v33 : pG 33 ∈ facetSection qG 24 := by
 refine ⟨(facet_listed_vertices_G 33).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG24v34 : pG 34 ∈ facetSection qG 24 := by
 refine ⟨(facet_listed_vertices_G 34).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG24v42 : pG 42 ∈ facetSection qG 24 := by
 refine ⟨(facet_listed_vertices_G 42).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G24 : affineDimension (facetSection qG 24) = 2 := by
 apply section_dimension_eq qG 24
 · intro hc
   apply not_collinear_of_minor (pG 33) (pG 34) (pG 42) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG24v33 | exact onG24v34 | exact onG24v42)
 · exact ⟨_,onG24v33⟩
end FullereneGeometry
