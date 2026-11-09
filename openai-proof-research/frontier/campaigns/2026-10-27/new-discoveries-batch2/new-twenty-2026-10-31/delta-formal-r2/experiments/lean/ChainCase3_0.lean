import ChainFirst3_0_0
import ChainFirst3_0_1
import ChainFirst3_0_2
import ChainFirst3_0_3
import ChainFirst3_0_4
import ChainFirst3_0_5
import ChainFirst3_0_6
import ChainFirst3_0_7
import ChainFirst3_0_8
import ChainFirst3_0_9
import ChainFirst3_0_10
namespace ChainPrefix
theorem case3_0 (b c m : V) (hf : Fits (first 3 b c 0 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((0:V) = 2 ∧ m = 6 ∨ 0 = 6 ∧ m = 2) := by
  fin_cases b
  · exact case3_0_0 c m hf
  · exact case3_0_1 c m hf
  · exact case3_0_2 c m hf
  · exact case3_0_3 c m hf
  · exact case3_0_4 c m hf
  · exact case3_0_5 c m hf
  · exact case3_0_6 c m hf
  · exact case3_0_7 c m hf
  · exact case3_0_8 c m hf
  · exact case3_0_9 c m hf
  · exact case3_0_10 c m hf
end ChainPrefix
