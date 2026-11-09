import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH16v04 : pH 4 ∈ facetSection qH 16 := by
 refine ⟨(facet_listed_vertices_H 4).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH16v05 : pH 5 ∈ facetSection qH 16 := by
 refine ⟨(facet_listed_vertices_H 5).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH16v07 : pH 7 ∈ facetSection qH 16 := by
 refine ⟨(facet_listed_vertices_H 7).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H16 : affineDimension (facetSection qH 16) = 2 := by
 apply section_dimension_eq qH 16
 · intro hc
   apply not_collinear_of_minor (pH 4) (pH 5) (pH 7) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH16v04 | exact onH16v05 | exact onH16v07)
 · exact ⟨_,onH16v04⟩
end FullereneGeometry
