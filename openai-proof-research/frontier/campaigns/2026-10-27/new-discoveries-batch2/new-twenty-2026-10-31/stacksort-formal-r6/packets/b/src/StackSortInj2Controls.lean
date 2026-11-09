import StackSortInj2Linkage
namespace StackSort
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem wrong_lower_row_rejected : tableValue 130 + 1 ≠ evalRhs tableValue 130 := by decide
theorem wrong_G_seed_rejected : G 3 ≠ 27 := by rw [G_seed (by decide)]; decide
end StackSort
