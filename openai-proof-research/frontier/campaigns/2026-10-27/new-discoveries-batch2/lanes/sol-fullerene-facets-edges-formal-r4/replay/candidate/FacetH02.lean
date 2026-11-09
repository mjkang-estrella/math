import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH02v22 : pH 22 ∈ facetSection qH 2 := by
 refine ⟨(facet_listed_vertices_H 22).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH02v23 : pH 23 ∈ facetSection qH 2 := by
 refine ⟨(facet_listed_vertices_H 23).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH02v27 : pH 27 ∈ facetSection qH 2 := by
 refine ⟨(facet_listed_vertices_H 27).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H02 : affineDimension (facetSection qH 2) = 2 := by
 apply section_dimension_eq qH 2
 · intro hc
   apply not_collinear_of_minor (pH 22) (pH 23) (pH 27) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH02v22 | exact onH02v23 | exact onH02v27)
 · exact ⟨_,onH02v22⟩
end FullereneGeometry
