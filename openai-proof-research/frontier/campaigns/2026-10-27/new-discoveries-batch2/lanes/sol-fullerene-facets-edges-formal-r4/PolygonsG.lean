import FacetsG
import HullG
import PolygonCore
noncomputable section
namespace FullereneGeometry
open TripleCertificates
theorem literal_polygon_G (i : Fin 32) :
 ConvexPolygon (facetSection qG i) (if i ∈ pentagonIdsG then 5 else 6) := by
 refine ⟨section_compact qG compact_G i, (facetSection_convexFace qG i).1,
   all_section_dimensions_G i, ?_, ?_, section_vertex_count_G i⟩
 · rw [section_vertices_G]
   exact (incidentG i).finite_toSet.image pG
 · rw [section_extremePoints_of_complete qG pG complete_vertices_G]
   exact section_hull_G i

theorem all_facets_polygons_G (F : Set E) (hf : GeometricFacet (poly qG) F) :
 ConvexPolygon F 5 ∨ ConvexPolygon F 6 := by
 obtain ⟨i,rfl⟩ := (all_geometric_facets_G F).mp hf
 by_cases h : i ∈ pentagonIdsG
 · left; simpa [h] using literal_polygon_G i
 · right; simpa [h] using literal_polygon_G i

end FullereneGeometry
