import CatalogueGraph
import GraphClosure1_000
namespace Nut8
theorem catalogue_simple_2 : ∀ code ∈ (GraphClosure1_000.targets : List ℕ), SimpleCode 2 code := by
  decide +kernel
end Nut8
