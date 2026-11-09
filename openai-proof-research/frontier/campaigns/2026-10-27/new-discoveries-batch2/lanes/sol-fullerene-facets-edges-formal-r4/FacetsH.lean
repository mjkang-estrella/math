import IncidenceRealH
import CompleteH
import FacetStandard
import FacetH00
import FacetH01
import FacetH02
import FacetH03
import FacetH04
import FacetH05
import FacetH06
import FacetH07
import FacetH08
import FacetH09
import FacetH10
import FacetH11
import FacetH12
import FacetH13
import FacetH14
import FacetH15
import FacetH16
import FacetH17
import FacetH18
import FacetH19
import FacetH20
import FacetH21
import FacetH22
import FacetH23
import FacetH24
import FacetH25
import FacetH26
import FacetH27
import FacetH28
import FacetH29
import FacetH30
import FacetH31
noncomputable section
namespace FullereneGeometry
open TripleCertificates
theorem all_section_dimensions_H (i : Fin 32) : affineDimension (facetSection qH i) = 2 := by
 fin_cases i
 · exact dimension_H00
 · exact dimension_H01
 · exact dimension_H02
 · exact dimension_H03
 · exact dimension_H04
 · exact dimension_H05
 · exact dimension_H06
 · exact dimension_H07
 · exact dimension_H08
 · exact dimension_H09
 · exact dimension_H10
 · exact dimension_H11
 · exact dimension_H12
 · exact dimension_H13
 · exact dimension_H14
 · exact dimension_H15
 · exact dimension_H16
 · exact dimension_H17
 · exact dimension_H18
 · exact dimension_H19
 · exact dimension_H20
 · exact dimension_H21
 · exact dimension_H22
 · exact dimension_H23
 · exact dimension_H24
 · exact dimension_H25
 · exact dimension_H26
 · exact dimension_H27
 · exact dimension_H28
 · exact dimension_H29
 · exact dimension_H30
 · exact dimension_H31
theorem all_sections_facets_H (i : Fin 32) : GeometricFacet (poly qH) (facetSection qH i) := by
 apply section_is_geometricFacet qH i
 · fin_cases i
   · exact ⟨_,onH00v00⟩
   · exact ⟨_,onH01v00⟩
   · exact ⟨_,onH02v22⟩
   · exact ⟨_,onH03v30⟩
   · exact ⟨_,onH04v42⟩
   · exact ⟨_,onH05v18⟩
   · exact ⟨_,onH06v24⟩
   · exact ⟨_,onH07v12⟩
   · exact ⟨_,onH08v10⟩
   · exact ⟨_,onH09v38⟩
   · exact ⟨_,onH10v45⟩
   · exact ⟨_,onH11v15⟩
   · exact ⟨_,onH12v00⟩
   · exact ⟨_,onH13v01⟩
   · exact ⟨_,onH14v02⟩
   · exact ⟨_,onH15v03⟩
   · exact ⟨_,onH16v04⟩
   · exact ⟨_,onH17v08⟩
   · exact ⟨_,onH18v06⟩
   · exact ⟨_,onH19v07⟩
   · exact ⟨_,onH20v22⟩
   · exact ⟨_,onH21v31⟩
   · exact ⟨_,onH22v26⟩
   · exact ⟨_,onH23v33⟩
   · exact ⟨_,onH24v34⟩
   · exact ⟨_,onH25v35⟩
   · exact ⟨_,onH26v28⟩
   · exact ⟨_,onH27v18⟩
   · exact ⟨_,onH28v45⟩
   · exact ⟨_,onH29v12⟩
   · exact ⟨_,onH30v48⟩
   · exact ⟨_,onH31v15⟩
 · exact all_section_dimensions_H i
theorem all_geometric_facets_H (F : Set E) :
 GeometricFacet (poly qH) F ↔ ∃ i, F = facetSection qH i := by
 constructor
 · exact geometricFacet_exhaustion qH
 · rintro ⟨i,rfl⟩; exact all_sections_facets_H i
theorem section_vertices_H (i : Fin 32) :
 (facetSection qH i).extremePoints ℝ = pH '' (↑(incidentH i) : Set (Fin 60)) :=
 section_extremePoints_image qH pH complete_vertices_H incidentH real_incidence_H i
theorem section_vertex_count_H (i : Fin 32) :
 ((facetSection qH i).extremePoints ℝ).ncard = if i ∈ pentagonIdsH then 5 else 6 := by
 rw [section_vertices_H, Set.ncard_image_of_injective _ points_injective_H,Set.ncard_coe_finset]
 exact incident_cardH i
theorem sections_distinct_H : Function.Injective (facetSection qH) := by
 intro i j he
 by_contra hn
 obtain ⟨v,hvi,hvj⟩ := incident_separateH i j hn
 have hv : pH v ∈ facetSection qH i :=
   ⟨(listed_vertices_H v).1,(real_incidence_H i v).mp hvi⟩
 rw [he] at hv
 exact hvj ((real_incidence_H j v).mpr hv.2)

theorem facet_count_H : ({F : Set E | GeometricFacet (poly qH) F}).ncard = 32 := by
 have he : {F : Set E | GeometricFacet (poly qH) F} = facetSection qH '' Set.univ := by
  ext F; simp only [Set.mem_ofPred_eq,all_geometric_facets_H,Set.mem_image,Set.mem_univ,true_and]
  exact exists_congr (fun i => eq_comm)
 rw [he,Set.ncard_image_of_injective _ sections_distinct_H]
 simp

theorem polygon_facet_image_H (k : ℕ) :
 {F : Set E | GeometricFacet (poly qH) F ∧ (F.extremePoints ℝ).ncard = k} =
 facetSection qH '' (↑(Finset.univ.filter (fun i : Fin 32 => (if i ∈ pentagonIdsH then 5 else 6) = k)) : Set (Fin 32)) := by
 ext F
 constructor
 · rintro ⟨hf,hk⟩
   obtain ⟨i,rfl⟩ := (all_geometric_facets_H F).mp hf
   exact ⟨i,by simpa [section_vertex_count_H] using hk,rfl⟩
 · rintro ⟨i,hi,rfl⟩
   exact ⟨all_sections_facets_H i, by simpa [section_vertex_count_H] using hi⟩

theorem pentagonal_facet_count_H :
 ({F : Set E | GeometricFacet (poly qH) F ∧ (F.extremePoints ℝ).ncard = 5}).ncard = 12 := by
 rw [polygon_facet_image_H,Set.ncard_image_of_injective _ sections_distinct_H,Set.ncard_coe_finset]
 decide +kernel

theorem hexagonal_facet_count_H :
 ({F : Set E | GeometricFacet (poly qH) F ∧ (F.extremePoints ℝ).ncard = 6}).ncard = 20 := by
 rw [polygon_facet_image_H,Set.ncard_image_of_injective _ sections_distinct_H,Set.ncard_coe_finset]
 decide +kernel


theorem facets_standard_equivalence_H (F : Set E) :
 GeometricFacet (poly qH) F ↔ MaximalProperFace (poly qH) F :=
 geometricFacet_iff_maximalProperFace qH all_section_dimensions_H F

end FullereneGeometry
