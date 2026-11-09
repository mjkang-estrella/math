import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH15v03 : pH 3 ∈ facetSection qH 15 := by
 refine ⟨(facet_listed_vertices_H 3).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH15v04 : pH 4 ∈ facetSection qH 15 := by
 refine ⟨(facet_listed_vertices_H 4).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH15v16 : pH 16 ∈ facetSection qH 15 := by
 refine ⟨(facet_listed_vertices_H 16).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H15 : affineDimension (facetSection qH 15) = 2 := by
 apply section_dimension_eq qH 15
 · intro hc
   apply not_collinear_of_minor (pH 3) (pH 4) (pH 16) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH15v03 | exact onH15v04 | exact onH15v16)
 · exact ⟨_,onH15v03⟩
end FullereneGeometry
