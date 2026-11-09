import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH17v08 : pH 8 ∈ facetSection qH 17 := by
 refine ⟨(facet_listed_vertices_H 8).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH17v09 : pH 9 ∈ facetSection qH 17 := by
 refine ⟨(facet_listed_vertices_H 9).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH17v22 : pH 22 ∈ facetSection qH 17 := by
 refine ⟨(facet_listed_vertices_H 22).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H17 : affineDimension (facetSection qH 17) = 2 := by
 apply section_dimension_eq qH 17
 · intro hc
   apply not_collinear_of_minor (pH 8) (pH 9) (pH 22) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH17v08 | exact onH17v09 | exact onH17v22)
 · exact ⟨_,onH17v08⟩
end FullereneGeometry
