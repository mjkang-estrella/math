import CompleteG
import Hulls
noncomputable section
namespace FullereneGeometry
theorem hull_G : poly qG = convexHull ℝ (Set.range pG) :=
 hull_of_complete_vertices qG compact_G pG complete_vertices_G
theorem section_hull_G (i : Fin 32) :
 facetSection qG i = convexHull ℝ {x ∈ Set.range pG | dot (qG i) x=1} :=
 section_hull_of_complete_vertices qG compact_G pG complete_vertices_G i
end FullereneGeometry
