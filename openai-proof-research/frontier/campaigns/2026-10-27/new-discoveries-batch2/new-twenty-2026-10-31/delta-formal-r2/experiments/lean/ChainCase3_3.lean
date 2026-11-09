import ChainFirst3_3_0
import ChainFirst3_3_1
import ChainFirst3_3_2
import ChainFirst3_3_3
import ChainFirst3_3_4
import ChainFirst3_3_5
import ChainFirst3_3_6
import ChainFirst3_3_7
import ChainFirst3_3_8
import ChainFirst3_3_9
import ChainFirst3_3_10
namespace ChainPrefix
theorem case3_3 (b c m : V) (hf : Fits (first 3 b c 3 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((3:V) = 2 ∧ m = 6 ∨ 3 = 6 ∧ m = 2) := by
  fin_cases b
  · exact case3_3_0 c m hf
  · exact case3_3_1 c m hf
  · exact case3_3_2 c m hf
  · exact case3_3_3 c m hf
  · exact case3_3_4 c m hf
  · exact case3_3_5 c m hf
  · exact case3_3_6 c m hf
  · exact case3_3_7 c m hf
  · exact case3_3_8 c m hf
  · exact case3_3_9 c m hf
  · exact case3_3_10 c m hf
end ChainPrefix
