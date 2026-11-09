import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH14v02 : pH 2 ∈ facetSection qH 14 := by
 refine ⟨(facet_listed_vertices_H 2).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH14v03 : pH 3 ∈ facetSection qH 14 := by
 refine ⟨(facet_listed_vertices_H 3).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH14v13 : pH 13 ∈ facetSection qH 14 := by
 refine ⟨(facet_listed_vertices_H 13).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H14 : affineDimension (facetSection qH 14) = 2 := by
 apply section_dimension_eq qH 14
 · intro hc
   apply not_collinear_of_minor (pH 2) (pH 3) (pH 13) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH14v02 | exact onH14v03 | exact onH14v13)
 · exact ⟨_,onH14v02⟩
end FullereneGeometry
