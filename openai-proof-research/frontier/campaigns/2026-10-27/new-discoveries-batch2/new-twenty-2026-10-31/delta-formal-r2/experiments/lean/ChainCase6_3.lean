import ChainFirst6_3_0
import ChainFirst6_3_1
import ChainFirst6_3_2
import ChainFirst6_3_3
import ChainFirst6_3_4
import ChainFirst6_3_5
import ChainFirst6_3_6
import ChainFirst6_3_7
import ChainFirst6_3_8
import ChainFirst6_3_9
import ChainFirst6_3_10
namespace ChainPrefix
theorem case6_3 (b c m : V) (hf : Fits (first 6 b c 3 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((3:V) = 3 ∧ m = 4 ∨ 3 = 4 ∧ m = 3) := by
  fin_cases b
  · exact case6_3_0 c m hf
  · exact case6_3_1 c m hf
  · exact case6_3_2 c m hf
  · exact case6_3_3 c m hf
  · exact case6_3_4 c m hf
  · exact case6_3_5 c m hf
  · exact case6_3_6 c m hf
  · exact case6_3_7 c m hf
  · exact case6_3_8 c m hf
  · exact case6_3_9 c m hf
  · exact case6_3_10 c m hf
end ChainPrefix
