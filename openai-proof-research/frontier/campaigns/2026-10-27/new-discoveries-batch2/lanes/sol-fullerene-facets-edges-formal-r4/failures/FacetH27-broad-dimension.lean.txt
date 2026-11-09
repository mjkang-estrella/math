import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH27v18 : pH 18 ∈ facetSection qH 27 := by
 refine ⟨(facet_listed_vertices_H 18).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH27v20 : pH 20 ∈ facetSection qH 27 := by
 refine ⟨(facet_listed_vertices_H 20).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH27v50 : pH 50 ∈ facetSection qH 27 := by
 refine ⟨(facet_listed_vertices_H 50).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H27 : affineDimension (facetSection qH 27) = 2 := by
 apply section_dimension_eq qH 27
 · intro hc
   apply not_collinear_of_minor (pH 18) (pH 20) (pH 50) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH27v18 | exact onH27v20 | exact onH27v50)
 · exact ⟨_,onH27v18⟩
end FullereneGeometry
