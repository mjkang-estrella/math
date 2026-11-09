import CatalogueGraph
import GraphClosure7_000
namespace Nut8
theorem catalogue_simple_8 : ∀ code ∈ (GraphClosure7_000.targets : List ℕ), SimpleCode 8 code := by
  decide +kernel
end Nut8
