import CatalogueGraph
import GraphClosure3_000
namespace Nut8
theorem catalogue_simple_4 : ∀ code ∈ (GraphClosure3_000.targets : List ℕ), SimpleCode 4 code := by
  decide +kernel
end Nut8
