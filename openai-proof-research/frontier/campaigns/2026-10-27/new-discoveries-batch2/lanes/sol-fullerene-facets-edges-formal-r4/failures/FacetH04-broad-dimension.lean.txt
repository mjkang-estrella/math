import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH04v42 : pH 42 ∈ facetSection qH 4 := by
 refine ⟨(facet_listed_vertices_H 42).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH04v43 : pH 43 ∈ facetSection qH 4 := by
 refine ⟨(facet_listed_vertices_H 43).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH04v47 : pH 47 ∈ facetSection qH 4 := by
 refine ⟨(facet_listed_vertices_H 47).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H04 : affineDimension (facetSection qH 4) = 2 := by
 apply section_dimension_eq qH 4
 · intro hc
   apply not_collinear_of_minor (pH 42) (pH 43) (pH 47) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH04v42 | exact onH04v43 | exact onH04v47)
 · exact ⟨_,onH04v42⟩
end FullereneGeometry
