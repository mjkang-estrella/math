import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH09v38 : pH 38 ∈ facetSection qH 9 := by
 refine ⟨(facet_listed_vertices_H 38).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH09v39 : pH 39 ∈ facetSection qH 9 := by
 refine ⟨(facet_listed_vertices_H 39).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH09v41 : pH 41 ∈ facetSection qH 9 := by
 refine ⟨(facet_listed_vertices_H 41).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H09 : affineDimension (facetSection qH 9) = 2 := by
 apply section_dimension_eq qH 9
 · intro hc
   apply not_collinear_of_minor (pH 38) (pH 39) (pH 41) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH09v38 | exact onH09v39 | exact onH09v41)
 · exact ⟨_,onH09v38⟩
end FullereneGeometry
