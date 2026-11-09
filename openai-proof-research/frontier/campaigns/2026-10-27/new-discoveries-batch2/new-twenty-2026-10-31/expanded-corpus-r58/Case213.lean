import Defs
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option warningAsError true
namespace Palette
theorem case213 : ∀ d e f g h i j : C, ¬ Good 2 1 3 d e f g h i j := by decide
end Palette
