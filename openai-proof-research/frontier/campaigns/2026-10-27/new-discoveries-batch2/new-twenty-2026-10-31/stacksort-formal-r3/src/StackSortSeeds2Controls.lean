import StackSortSeeds2Final
namespace StackSort.Seeds2
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem wrong_seed_rejected : tableX 5 1 1 ≠ 2357 := by decide
 theorem wrong_unary_weight_rejected :
    (∑ t ∈ Finset.range 3, ∑ u ∈ Finset.range 3,
      tableX 1 t u) ≠ tableI 2 1 1 := by decide
 theorem positive_seed5 : tableX 5 1 1 = 2356 := by decide
 theorem positive_seed6 : tableX 6 1 1 = 29064 := by decide
end StackSort.Seeds2
