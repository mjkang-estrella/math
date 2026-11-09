import ChainPrefix
namespace ChainPrefix
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
 theorem first3 : ∀ l b c m : V, Fits (first 3 b c l m) →
    ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧
    ((l = 2 ∧ m = 6) ∨ (l = 6 ∧ m = 2)) := by
  unfold Fits first tri dbl Literal.pairCount Concrete.g7
  decide +kernel
end ChainPrefix
