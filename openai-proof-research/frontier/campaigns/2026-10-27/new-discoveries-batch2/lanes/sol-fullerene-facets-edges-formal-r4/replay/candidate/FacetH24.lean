import FeasibleH
import FacetDimension
noncomputable section
namespace FullereneGeometry
theorem onH24v34 : pH 34 ∈ facetSection qH 24 := by
 refine ⟨(facet_listed_vertices_H 34).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH24v35 : pH 35 ∈ facetSection qH 24 := by
 refine ⟨(facet_listed_vertices_H 35).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem onH24v43 : pH 43 ∈ facetSection qH 24 := by
 refine ⟨(facet_listed_vertices_H 43).1, ?_⟩
 norm_num [dot,qH,pH,Fin.sum_univ_succ]
theorem dimension_H24 : affineDimension (facetSection qH 24) = 2 := by
 apply section_dimension_eq qH 24
 · intro hc
   apply not_collinear_of_minor (pH 34) (pH 35) (pH 43) 0 1
     (by norm_num [pH])
   exact hc.subset (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> first | exact onH24v34 | exact onH24v35 | exact onH24v43)
 · exact ⟨_,onH24v34⟩
end FullereneGeometry
