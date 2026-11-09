import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH20v22 : pH 22 ∈ facetSection qH 20 := by
 refine ⟨(facet_listed_vertices_H 22).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH20v25 : pH 25 ∈ facetSection qH 20 := by
 refine ⟨(facet_listed_vertices_H 25).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH20v30 : pH 30 ∈ facetSection qH 20 := by
 refine ⟨(facet_listed_vertices_H 30).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H20 : affineDimension (facetSection qH 20) = 2 := by
 apply section_dimension_eq qH 20
 · intro hc
   apply not_collinear_of_minor (pH 22) (pH 25) (pH 30) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH20v22 | exact onH20v25 | exact onH20v30)
 · exact ⟨_,onH20v22⟩
end FullereneGeometry
