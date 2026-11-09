import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH31v15 : pH 15 ∈ facetSection qH 31 := by
 refine ⟨(facet_listed_vertices_H 15).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH31v17 : pH 17 ∈ facetSection qH 31 := by
 refine ⟨(facet_listed_vertices_H 17).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH31v54 : pH 54 ∈ facetSection qH 31 := by
 refine ⟨(facet_listed_vertices_H 54).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H31 : affineDimension (facetSection qH 31) = 2 := by
 apply section_dimension_eq qH 31
 · intro hc
   apply not_collinear_of_minor (pH 15) (pH 17) (pH 54) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH31v15 | exact onH31v17 | exact onH31v54)
 · exact ⟨_,onH31v15⟩
end FullereneGeometry
