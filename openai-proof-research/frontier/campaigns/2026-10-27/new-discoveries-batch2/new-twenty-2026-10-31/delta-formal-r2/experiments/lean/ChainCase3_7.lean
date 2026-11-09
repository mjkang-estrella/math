import ChainFirst3_7_0
import ChainFirst3_7_1
import ChainFirst3_7_2
import ChainFirst3_7_3
import ChainFirst3_7_4
import ChainFirst3_7_5
import ChainFirst3_7_6
import ChainFirst3_7_7
import ChainFirst3_7_8
import ChainFirst3_7_9
import ChainFirst3_7_10
namespace ChainPrefix
theorem case3_7 (b c m : V) (hf : Fits (first 3 b c 7 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((7:V) = 2 ∧ m = 6 ∨ 7 = 6 ∧ m = 2) := by
  fin_cases b
  · exact case3_7_0 c m hf
  · exact case3_7_1 c m hf
  · exact case3_7_2 c m hf
  · exact case3_7_3 c m hf
  · exact case3_7_4 c m hf
  · exact case3_7_5 c m hf
  · exact case3_7_6 c m hf
  · exact case3_7_7 c m hf
  · exact case3_7_8 c m hf
  · exact case3_7_9 c m hf
  · exact case3_7_10 c m hf
end ChainPrefix
