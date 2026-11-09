import CompleteH
import Hulls
noncomputable section
namespace FullereneGeometry
theorem hull_H : poly qH = convexHull ℝ (Set.range pH) :=
 hull_of_complete_vertices qH compact_H pH complete_vertices_H
theorem section_hull_H (i : Fin 32) :
 facetSection qH i = convexHull ℝ {x ∈ Set.range pH | dot (qH i) x=1} :=
 section_hull_of_complete_vertices qH compact_H pH complete_vertices_H i
end FullereneGeometry
