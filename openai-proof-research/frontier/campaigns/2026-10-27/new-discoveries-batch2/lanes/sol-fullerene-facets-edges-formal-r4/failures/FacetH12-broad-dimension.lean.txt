import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH12v00 : pH 0 ∈ facetSection qH 12 := by
 refine ⟨(facet_listed_vertices_H 0).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH12v01 : pH 1 ∈ facetSection qH 12 := by
 refine ⟨(facet_listed_vertices_H 1).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH12v06 : pH 6 ∈ facetSection qH 12 := by
 refine ⟨(facet_listed_vertices_H 6).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H12 : affineDimension (facetSection qH 12) = 2 := by
 apply section_dimension_eq qH 12
 · intro hc
   apply not_collinear_of_minor (pH 0) (pH 1) (pH 6) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH12v00 | exact onH12v01 | exact onH12v06)
 · exact ⟨_,onH12v00⟩
end FullereneGeometry
