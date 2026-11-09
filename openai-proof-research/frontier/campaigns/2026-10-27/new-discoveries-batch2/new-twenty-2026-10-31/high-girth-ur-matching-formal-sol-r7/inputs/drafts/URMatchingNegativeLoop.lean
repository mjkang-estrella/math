module
import URMatchingControls
namespace URMatching.Controls
-- Intentional mutation: a singleton diagonal pair must NOT be an edge/matching.
example : IsMatching K2 ({s(0, 0)} : Finset (Sym2 (Fin 2))) := by
  simp [IsMatching]
end URMatching.Controls
