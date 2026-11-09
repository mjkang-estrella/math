import StackSortBasic
noncomputable section
namespace StackSort
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem P_four : P 4 = 224 := by decide
end StackSort
