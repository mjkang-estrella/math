import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH23v33 : pH 33 ∈ facetSection qH 23 := by
 refine ⟨(facet_listed_vertices_H 33).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH23v34 : pH 34 ∈ facetSection qH 23 := by
 refine ⟨(facet_listed_vertices_H 34).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH23v37 : pH 37 ∈ facetSection qH 23 := by
 refine ⟨(facet_listed_vertices_H 37).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H23 : affineDimension (facetSection qH 23) = 2 := by
 apply section_dimension_eq qH 23
 · intro hc
   apply not_collinear_of_minor (pH 33) (pH 34) (pH 37) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH23v33 | exact onH23v34 | exact onH23v37)
 · exact ⟨_,onH23v33⟩
end FullereneGeometry
