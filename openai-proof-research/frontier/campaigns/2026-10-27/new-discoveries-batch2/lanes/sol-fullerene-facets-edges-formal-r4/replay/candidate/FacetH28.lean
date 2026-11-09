import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH28v45 : pH 45 ∈ facetSection qH 28 := by
 refine ⟨(facet_listed_vertices_H 45).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH28v47 : pH 47 ∈ facetSection qH 28 := by
 refine ⟨(facet_listed_vertices_H 47).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH28v51 : pH 51 ∈ facetSection qH 28 := by
 refine ⟨(facet_listed_vertices_H 51).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H28 : affineDimension (facetSection qH 28) = 2 := by
 apply section_dimension_eq qH 28
 · intro hc
   apply not_collinear_of_minor (pH 45) (pH 47) (pH 51) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH28v45 | exact onH28v47 | exact onH28v51)
 · exact ⟨_,onH28v45⟩
end FullereneGeometry
