import ChainFirst6_2_0
import ChainFirst6_2_1
import ChainFirst6_2_2
import ChainFirst6_2_3
import ChainFirst6_2_4
import ChainFirst6_2_5
import ChainFirst6_2_6
import ChainFirst6_2_7
import ChainFirst6_2_8
import ChainFirst6_2_9
import ChainFirst6_2_10
namespace ChainPrefix
theorem case6_2 (b c m : V) (hf : Fits (first 6 b c 2 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((2:V) = 3 ∧ m = 4 ∨ 2 = 4 ∧ m = 3) := by
  fin_cases b
  · exact case6_2_0 c m hf
  · exact case6_2_1 c m hf
  · exact case6_2_2 c m hf
  · exact case6_2_3 c m hf
  · exact case6_2_4 c m hf
  · exact case6_2_5 c m hf
  · exact case6_2_6 c m hf
  · exact case6_2_7 c m hf
  · exact case6_2_8 c m hf
  · exact case6_2_9 c m hf
  · exact case6_2_10 c m hf
end ChainPrefix
