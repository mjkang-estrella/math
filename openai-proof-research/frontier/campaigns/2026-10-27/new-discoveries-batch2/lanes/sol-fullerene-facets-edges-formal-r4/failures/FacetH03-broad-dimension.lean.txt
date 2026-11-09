import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH03v30 : pH 30 ∈ facetSection qH 3 := by
 refine ⟨(facet_listed_vertices_H 30).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH03v31 : pH 31 ∈ facetSection qH 3 := by
 refine ⟨(facet_listed_vertices_H 31).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH03v33 : pH 33 ∈ facetSection qH 3 := by
 refine ⟨(facet_listed_vertices_H 33).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H03 : affineDimension (facetSection qH 3) = 2 := by
 apply section_dimension_eq qH 3
 · intro hc
   apply not_collinear_of_minor (pH 30) (pH 31) (pH 33) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH03v30 | exact onH03v31 | exact onH03v33)
 · exact ⟨_,onH03v30⟩
end FullereneGeometry
