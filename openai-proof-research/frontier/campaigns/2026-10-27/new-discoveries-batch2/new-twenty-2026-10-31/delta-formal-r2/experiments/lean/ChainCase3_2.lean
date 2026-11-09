import ChainFirst3_2_0
import ChainFirst3_2_1
import ChainFirst3_2_2
import ChainFirst3_2_3
import ChainFirst3_2_4
import ChainFirst3_2_5
import ChainFirst3_2_6
import ChainFirst3_2_7
import ChainFirst3_2_8
import ChainFirst3_2_9
import ChainFirst3_2_10
namespace ChainPrefix
theorem case3_2 (b c m : V) (hf : Fits (first 3 b c 2 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((2:V) = 2 ∧ m = 6 ∨ 2 = 6 ∧ m = 2) := by
  fin_cases b
  · exact case3_2_0 c m hf
  · exact case3_2_1 c m hf
  · exact case3_2_2 c m hf
  · exact case3_2_3 c m hf
  · exact case3_2_4 c m hf
  · exact case3_2_5 c m hf
  · exact case3_2_6 c m hf
  · exact case3_2_7 c m hf
  · exact case3_2_8 c m hf
  · exact case3_2_9 c m hf
  · exact case3_2_10 c m hf
end ChainPrefix
