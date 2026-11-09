import ChainFirst3_4_0
import ChainFirst3_4_1
import ChainFirst3_4_2
import ChainFirst3_4_3
import ChainFirst3_4_4
import ChainFirst3_4_5
import ChainFirst3_4_6
import ChainFirst3_4_7
import ChainFirst3_4_8
import ChainFirst3_4_9
import ChainFirst3_4_10
namespace ChainPrefix
theorem case3_4 (b c m : V) (hf : Fits (first 3 b c 4 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((4:V) = 2 ∧ m = 6 ∨ 4 = 6 ∧ m = 2) := by
  fin_cases b
  · exact case3_4_0 c m hf
  · exact case3_4_1 c m hf
  · exact case3_4_2 c m hf
  · exact case3_4_3 c m hf
  · exact case3_4_4 c m hf
  · exact case3_4_5 c m hf
  · exact case3_4_6 c m hf
  · exact case3_4_7 c m hf
  · exact case3_4_8 c m hf
  · exact case3_4_9 c m hf
  · exact case3_4_10 c m hf
end ChainPrefix
