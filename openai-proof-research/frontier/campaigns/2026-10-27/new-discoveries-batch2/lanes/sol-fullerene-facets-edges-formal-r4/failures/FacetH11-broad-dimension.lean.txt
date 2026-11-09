import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH11v15 : pH 15 ∈ facetSection qH 11 := by
 refine ⟨(facet_listed_vertices_H 15).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH11v16 : pH 16 ∈ facetSection qH 11 := by
 refine ⟨(facet_listed_vertices_H 16).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH11v20 : pH 20 ∈ facetSection qH 11 := by
 refine ⟨(facet_listed_vertices_H 20).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H11 : affineDimension (facetSection qH 11) = 2 := by
 apply section_dimension_eq qH 11
 · intro hc
   apply not_collinear_of_minor (pH 15) (pH 16) (pH 20) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH11v15 | exact onH11v16 | exact onH11v20)
 · exact ⟨_,onH11v15⟩
end FullereneGeometry
