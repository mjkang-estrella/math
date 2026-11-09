import FeasibleG
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onG09v37 : pG 37 ∈ facetSection qG 9 := by
 refine ⟨(facet_listed_vertices_G 37).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG09v38 : pG 38 ∈ facetSection qG 9 := by
 refine ⟨(facet_listed_vertices_G 38).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem onG09v40 : pG 40 ∈ facetSection qG 9 := by
 refine ⟨(facet_listed_vertices_G 40).1, ?_⟩
 norm_num [dot,qG,pG,Fin.sum_univ_succ]
theorem dimension_G09 : affineDimension (facetSection qG 9) = 2 := by
 apply section_dimension_eq qG 9
 · intro hc
   apply not_collinear_of_minor (pG 37) (pG 38) (pG 40) 0 1
     (by norm_num [pG])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onG09v37 | exact onG09v38 | exact onG09v40)
 · exact ⟨_,onG09v37⟩
end FullereneGeometry
