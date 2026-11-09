import CatalogueGraph
import GraphClosure5_000
namespace Nut8
theorem catalogue_simple_6 : ∀ code ∈ (GraphClosure5_000.targets : List ℕ), SimpleCode 6 code := by
  decide +kernel
end Nut8
