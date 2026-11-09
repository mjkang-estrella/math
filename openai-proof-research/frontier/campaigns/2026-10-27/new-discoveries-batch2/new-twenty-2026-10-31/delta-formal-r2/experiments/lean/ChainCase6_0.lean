import ChainFirst6_0_0
import ChainFirst6_0_1
import ChainFirst6_0_2
import ChainFirst6_0_3
import ChainFirst6_0_4
import ChainFirst6_0_5
import ChainFirst6_0_6
import ChainFirst6_0_7
import ChainFirst6_0_8
import ChainFirst6_0_9
import ChainFirst6_0_10
namespace ChainPrefix
theorem case6_0 (b c m : V) (hf : Fits (first 6 b c 0 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((0:V) = 3 ∧ m = 4 ∨ 0 = 4 ∧ m = 3) := by
  fin_cases b
  · exact case6_0_0 c m hf
  · exact case6_0_1 c m hf
  · exact case6_0_2 c m hf
  · exact case6_0_3 c m hf
  · exact case6_0_4 c m hf
  · exact case6_0_5 c m hf
  · exact case6_0_6 c m hf
  · exact case6_0_7 c m hf
  · exact case6_0_8 c m hf
  · exact case6_0_9 c m hf
  · exact case6_0_10 c m hf
end ChainPrefix
