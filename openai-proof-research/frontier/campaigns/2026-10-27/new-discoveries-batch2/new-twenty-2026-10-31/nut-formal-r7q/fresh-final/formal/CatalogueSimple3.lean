import CatalogueGraph
import GraphClosure2_000
namespace Nut8
theorem catalogue_simple_3 : ∀ code ∈ (GraphClosure2_000.targets : List ℕ), SimpleCode 3 code := by
  decide +kernel
end Nut8
