import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH05v18 : pH 18 ∈ facetSection qH 5 := by
 refine ⟨(facet_listed_vertices_H 18).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH05v19 : pH 19 ∈ facetSection qH 5 := by
 refine ⟨(facet_listed_vertices_H 19).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH05v21 : pH 21 ∈ facetSection qH 5 := by
 refine ⟨(facet_listed_vertices_H 21).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H05 : affineDimension (facetSection qH 5) = 2 := by
 apply section_dimension_eq qH 5
 · intro hc
   apply not_collinear_of_minor (pH 18) (pH 19) (pH 21) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH05v18 | exact onH05v19 | exact onH05v21)
 · exact ⟨_,onH05v18⟩
end FullereneGeometry
