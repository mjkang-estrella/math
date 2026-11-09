import FacetsH
import HullH
import PolygonCore
noncomputable section
namespace FullereneGeometry
open TripleCertificates
theorem literal_polygon_H (i : Fin 32) :
 ConvexPolygon (facetSection qH i) (if i ∈ pentagonIdsH then 5 else 6) := by
 refine ⟨section_compact qH compact_H i, (facetSection_convexFace qH i).1,
   all_section_dimensions_H i, ?_, ?_, section_vertex_count_H i⟩
 · rw [section_vertices_H]
   exact (incidentH i).finite_toSet.image pH
 · rw [section_extremePoints_of_complete qH pH complete_vertices_H]
   exact section_hull_H i

theorem all_facets_polygons_H (F : Set E) (hf : GeometricFacet (poly qH) F) :
 ConvexPolygon F 5 ∨ ConvexPolygon F 6 := by
 obtain ⟨i,rfl⟩ := (all_geometric_facets_H F).mp hf
 by_cases h : i ∈ pentagonIdsH
 · left; simpa [h] using literal_polygon_H i
 · right; simpa [h] using literal_polygon_H i

end FullereneGeometry
