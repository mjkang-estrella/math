import ChainFirst3_1_0
import ChainFirst3_1_1
import ChainFirst3_1_2
import ChainFirst3_1_3
import ChainFirst3_1_4
import ChainFirst3_1_5
import ChainFirst3_1_6
import ChainFirst3_1_7
import ChainFirst3_1_8
import ChainFirst3_1_9
import ChainFirst3_1_10
namespace ChainPrefix
theorem case3_1 (b c m : V) (hf : Fits (first 3 b c 1 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((1:V) = 2 ∧ m = 6 ∨ 1 = 6 ∧ m = 2) := by
  fin_cases b
  · exact case3_1_0 c m hf
  · exact case3_1_1 c m hf
  · exact case3_1_2 c m hf
  · exact case3_1_3 c m hf
  · exact case3_1_4 c m hf
  · exact case3_1_5 c m hf
  · exact case3_1_6 c m hf
  · exact case3_1_7 c m hf
  · exact case3_1_8 c m hf
  · exact case3_1_9 c m hf
  · exact case3_1_10 c m hf
end ChainPrefix
