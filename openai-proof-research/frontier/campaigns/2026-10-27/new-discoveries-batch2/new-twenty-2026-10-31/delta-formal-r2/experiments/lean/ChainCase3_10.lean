import ChainFirst3_10_0
import ChainFirst3_10_1
import ChainFirst3_10_2
import ChainFirst3_10_3
import ChainFirst3_10_4
import ChainFirst3_10_5
import ChainFirst3_10_6
import ChainFirst3_10_7
import ChainFirst3_10_8
import ChainFirst3_10_9
import ChainFirst3_10_10
namespace ChainPrefix
theorem case3_10 (b c m : V) (hf : Fits (first 3 b c 10 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((10:V) = 2 ∧ m = 6 ∨ 10 = 6 ∧ m = 2) := by
  fin_cases b
  · exact case3_10_0 c m hf
  · exact case3_10_1 c m hf
  · exact case3_10_2 c m hf
  · exact case3_10_3 c m hf
  · exact case3_10_4 c m hf
  · exact case3_10_5 c m hf
  · exact case3_10_6 c m hf
  · exact case3_10_7 c m hf
  · exact case3_10_8 c m hf
  · exact case3_10_9 c m hf
  · exact case3_10_10 c m hf
end ChainPrefix
