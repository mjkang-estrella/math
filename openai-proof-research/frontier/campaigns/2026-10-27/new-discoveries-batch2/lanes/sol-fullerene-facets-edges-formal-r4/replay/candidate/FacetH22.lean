import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH22v26 : pH 26 ∈ facetSection qH 22 := by
 refine ⟨(facet_listed_vertices_H 26).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH22v27 : pH 27 ∈ facetSection qH 22 := by
 refine ⟨(facet_listed_vertices_H 27).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH22v32 : pH 32 ∈ facetSection qH 22 := by
 refine ⟨(facet_listed_vertices_H 32).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H22 : affineDimension (facetSection qH 22) = 2 := by
 apply section_dimension_eq qH 22
 · intro hc
   apply not_collinear_of_minor (pH 26) (pH 27) (pH 32) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH22v26 | exact onH22v27 | exact onH22v32)
 · exact ⟨_,onH22v26⟩
end FullereneGeometry
