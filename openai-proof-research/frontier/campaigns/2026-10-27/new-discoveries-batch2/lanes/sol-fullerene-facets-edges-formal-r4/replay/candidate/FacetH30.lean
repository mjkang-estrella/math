import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH30v48 : pH 48 ∈ facetSection qH 30 := by
 refine ⟨(facet_listed_vertices_H 48).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH30v49 : pH 49 ∈ facetSection qH 30 := by
 refine ⟨(facet_listed_vertices_H 49).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH30v56 : pH 56 ∈ facetSection qH 30 := by
 refine ⟨(facet_listed_vertices_H 56).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H30 : affineDimension (facetSection qH 30) = 2 := by
 apply section_dimension_eq qH 30
 · intro hc
   apply not_collinear_of_minor (pH 48) (pH 49) (pH 56) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH30v48 | exact onH30v49 | exact onH30v56)
 · exact ⟨_,onH30v48⟩
end FullereneGeometry
