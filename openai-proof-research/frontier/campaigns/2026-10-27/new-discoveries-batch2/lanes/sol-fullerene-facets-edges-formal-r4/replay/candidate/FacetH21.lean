import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH21v31 : pH 31 ∈ facetSection qH 21 := by
 refine ⟨(facet_listed_vertices_H 31).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH21v32 : pH 32 ∈ facetSection qH 21 := by
 refine ⟨(facet_listed_vertices_H 32).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH21v36 : pH 36 ∈ facetSection qH 21 := by
 refine ⟨(facet_listed_vertices_H 36).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H21 : affineDimension (facetSection qH 21) = 2 := by
 apply section_dimension_eq qH 21
 · intro hc
   apply not_collinear_of_minor (pH 31) (pH 32) (pH 36) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH21v31 | exact onH21v32 | exact onH21v36)
 · exact ⟨_,onH21v31⟩
end FullereneGeometry
