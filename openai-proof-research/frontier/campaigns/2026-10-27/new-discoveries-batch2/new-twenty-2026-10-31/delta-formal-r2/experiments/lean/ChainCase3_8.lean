import ChainFirst3_8_0
import ChainFirst3_8_1
import ChainFirst3_8_2
import ChainFirst3_8_3
import ChainFirst3_8_4
import ChainFirst3_8_5
import ChainFirst3_8_6
import ChainFirst3_8_7
import ChainFirst3_8_8
import ChainFirst3_8_9
import ChainFirst3_8_10
namespace ChainPrefix
theorem case3_8 (b c m : V) (hf : Fits (first 3 b c 8 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((8:V) = 2 ∧ m = 6 ∨ 8 = 6 ∧ m = 2) := by
  fin_cases b
  · exact case3_8_0 c m hf
  · exact case3_8_1 c m hf
  · exact case3_8_2 c m hf
  · exact case3_8_3 c m hf
  · exact case3_8_4 c m hf
  · exact case3_8_5 c m hf
  · exact case3_8_6 c m hf
  · exact case3_8_7 c m hf
  · exact case3_8_8 c m hf
  · exact case3_8_9 c m hf
  · exact case3_8_10 c m hf
end ChainPrefix
