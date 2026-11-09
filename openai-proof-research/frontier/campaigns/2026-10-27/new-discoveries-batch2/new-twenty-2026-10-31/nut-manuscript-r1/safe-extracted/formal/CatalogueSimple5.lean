import CatalogueGraph
import GraphClosure4_000
namespace Nut8
theorem catalogue_simple_5 : ∀ code ∈ (GraphClosure4_000.targets : List ℕ), SimpleCode 5 code := by
  decide +kernel
end Nut8
