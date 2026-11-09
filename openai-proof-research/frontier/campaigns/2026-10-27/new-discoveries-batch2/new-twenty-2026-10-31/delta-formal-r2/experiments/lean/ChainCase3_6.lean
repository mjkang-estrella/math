import ChainFirst3_6_0
import ChainFirst3_6_1
import ChainFirst3_6_2
import ChainFirst3_6_3
import ChainFirst3_6_4
import ChainFirst3_6_5
import ChainFirst3_6_6
import ChainFirst3_6_7
import ChainFirst3_6_8
import ChainFirst3_6_9
import ChainFirst3_6_10
namespace ChainPrefix
theorem case3_6 (b c m : V) (hf : Fits (first 3 b c 6 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((6:V) = 2 ∧ m = 6 ∨ 6 = 6 ∧ m = 2) := by
  fin_cases b
  · exact case3_6_0 c m hf
  · exact case3_6_1 c m hf
  · exact case3_6_2 c m hf
  · exact case3_6_3 c m hf
  · exact case3_6_4 c m hf
  · exact case3_6_5 c m hf
  · exact case3_6_6 c m hf
  · exact case3_6_7 c m hf
  · exact case3_6_8 c m hf
  · exact case3_6_9 c m hf
  · exact case3_6_10 c m hf
end ChainPrefix
