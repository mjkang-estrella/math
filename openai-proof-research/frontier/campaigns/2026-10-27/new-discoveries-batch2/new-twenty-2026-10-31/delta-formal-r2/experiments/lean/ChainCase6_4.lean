import ChainFirst6_4_0
import ChainFirst6_4_1
import ChainFirst6_4_2
import ChainFirst6_4_3
import ChainFirst6_4_4
import ChainFirst6_4_5
import ChainFirst6_4_6
import ChainFirst6_4_7
import ChainFirst6_4_8
import ChainFirst6_4_9
import ChainFirst6_4_10
namespace ChainPrefix
theorem case6_4 (b c m : V) (hf : Fits (first 6 b c 4 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((4:V) = 3 ∧ m = 4 ∨ 4 = 4 ∧ m = 3) := by
  fin_cases b
  · exact case6_4_0 c m hf
  · exact case6_4_1 c m hf
  · exact case6_4_2 c m hf
  · exact case6_4_3 c m hf
  · exact case6_4_4 c m hf
  · exact case6_4_5 c m hf
  · exact case6_4_6 c m hf
  · exact case6_4_7 c m hf
  · exact case6_4_8 c m hf
  · exact case6_4_9 c m hf
  · exact case6_4_10 c m hf
end ChainPrefix
