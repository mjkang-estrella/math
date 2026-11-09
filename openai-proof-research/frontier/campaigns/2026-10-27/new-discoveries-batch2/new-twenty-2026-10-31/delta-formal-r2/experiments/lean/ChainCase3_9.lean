import ChainFirst3_9_0
import ChainFirst3_9_1
import ChainFirst3_9_2
import ChainFirst3_9_3
import ChainFirst3_9_4
import ChainFirst3_9_5
import ChainFirst3_9_6
import ChainFirst3_9_7
import ChainFirst3_9_8
import ChainFirst3_9_9
import ChainFirst3_9_10
namespace ChainPrefix
theorem case3_9 (b c m : V) (hf : Fits (first 3 b c 9 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((9:V) = 2 ∧ m = 6 ∨ 9 = 6 ∧ m = 2) := by
  fin_cases b
  · exact case3_9_0 c m hf
  · exact case3_9_1 c m hf
  · exact case3_9_2 c m hf
  · exact case3_9_3 c m hf
  · exact case3_9_4 c m hf
  · exact case3_9_5 c m hf
  · exact case3_9_6 c m hf
  · exact case3_9_7 c m hf
  · exact case3_9_8 c m hf
  · exact case3_9_9 c m hf
  · exact case3_9_10 c m hf
end ChainPrefix
