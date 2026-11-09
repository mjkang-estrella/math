import ChainFirst6_10_0
import ChainFirst6_10_1
import ChainFirst6_10_2
import ChainFirst6_10_3
import ChainFirst6_10_4
import ChainFirst6_10_5
import ChainFirst6_10_6
import ChainFirst6_10_7
import ChainFirst6_10_8
import ChainFirst6_10_9
import ChainFirst6_10_10
namespace ChainPrefix
theorem case6_10 (b c m : V) (hf : Fits (first 6 b c 10 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((10:V) = 3 ∧ m = 4 ∨ 10 = 4 ∧ m = 3) := by
  fin_cases b
  · exact case6_10_0 c m hf
  · exact case6_10_1 c m hf
  · exact case6_10_2 c m hf
  · exact case6_10_3 c m hf
  · exact case6_10_4 c m hf
  · exact case6_10_5 c m hf
  · exact case6_10_6 c m hf
  · exact case6_10_7 c m hf
  · exact case6_10_8 c m hf
  · exact case6_10_9 c m hf
  · exact case6_10_10 c m hf
end ChainPrefix
