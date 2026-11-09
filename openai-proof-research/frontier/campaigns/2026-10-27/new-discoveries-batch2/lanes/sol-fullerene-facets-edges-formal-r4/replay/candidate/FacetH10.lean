import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH10v45 : pH 45 ∈ facetSection qH 10 := by
 refine ⟨(facet_listed_vertices_H 45).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH10v46 : pH 46 ∈ facetSection qH 10 := by
 refine ⟨(facet_listed_vertices_H 46).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH10v49 : pH 49 ∈ facetSection qH 10 := by
 refine ⟨(facet_listed_vertices_H 49).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H10 : affineDimension (facetSection qH 10) = 2 := by
 apply section_dimension_eq qH 10
 · intro hc
   apply not_collinear_of_minor (pH 45) (pH 46) (pH 49) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH10v45 | exact onH10v46 | exact onH10v49)
 · exact ⟨_,onH10v45⟩
end FullereneGeometry
