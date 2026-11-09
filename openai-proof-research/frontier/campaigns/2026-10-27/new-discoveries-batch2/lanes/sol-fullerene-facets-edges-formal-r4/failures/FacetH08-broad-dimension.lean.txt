import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH08v10 : pH 10 ∈ facetSection qH 8 := by
 refine ⟨(facet_listed_vertices_H 10).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH08v11 : pH 11 ∈ facetSection qH 8 := by
 refine ⟨(facet_listed_vertices_H 11).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH08v14 : pH 14 ∈ facetSection qH 8 := by
 refine ⟨(facet_listed_vertices_H 14).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H08 : affineDimension (facetSection qH 8) = 2 := by
 apply section_dimension_eq qH 8
 · intro hc
   apply not_collinear_of_minor (pH 10) (pH 11) (pH 14) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH08v10 | exact onH08v11 | exact onH08v14)
 · exact ⟨_,onH08v10⟩
end FullereneGeometry
