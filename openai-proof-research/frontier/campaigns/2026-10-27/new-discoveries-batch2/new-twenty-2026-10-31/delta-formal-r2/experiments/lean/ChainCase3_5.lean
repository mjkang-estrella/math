import ChainFirst3_5_0
import ChainFirst3_5_1
import ChainFirst3_5_2
import ChainFirst3_5_3
import ChainFirst3_5_4
import ChainFirst3_5_5
import ChainFirst3_5_6
import ChainFirst3_5_7
import ChainFirst3_5_8
import ChainFirst3_5_9
import ChainFirst3_5_10
namespace ChainPrefix
theorem case3_5 (b c m : V) (hf : Fits (first 3 b c 5 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((5:V) = 2 ∧ m = 6 ∨ 5 = 6 ∧ m = 2) := by
  fin_cases b
  · exact case3_5_0 c m hf
  · exact case3_5_1 c m hf
  · exact case3_5_2 c m hf
  · exact case3_5_3 c m hf
  · exact case3_5_4 c m hf
  · exact case3_5_5 c m hf
  · exact case3_5_6 c m hf
  · exact case3_5_7 c m hf
  · exact case3_5_8 c m hf
  · exact case3_5_9 c m hf
  · exact case3_5_10 c m hf
end ChainPrefix
