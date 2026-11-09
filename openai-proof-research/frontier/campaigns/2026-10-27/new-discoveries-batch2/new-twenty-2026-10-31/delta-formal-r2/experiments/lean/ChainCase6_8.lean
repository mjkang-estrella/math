import ChainFirst6_8_0
import ChainFirst6_8_1
import ChainFirst6_8_2
import ChainFirst6_8_3
import ChainFirst6_8_4
import ChainFirst6_8_5
import ChainFirst6_8_6
import ChainFirst6_8_7
import ChainFirst6_8_8
import ChainFirst6_8_9
import ChainFirst6_8_10
namespace ChainPrefix
theorem case6_8 (b c m : V) (hf : Fits (first 6 b c 8 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((8:V) = 3 ∧ m = 4 ∨ 8 = 4 ∧ m = 3) := by
  fin_cases b
  · exact case6_8_0 c m hf
  · exact case6_8_1 c m hf
  · exact case6_8_2 c m hf
  · exact case6_8_3 c m hf
  · exact case6_8_4 c m hf
  · exact case6_8_5 c m hf
  · exact case6_8_6 c m hf
  · exact case6_8_7 c m hf
  · exact case6_8_8 c m hf
  · exact case6_8_9 c m hf
  · exact case6_8_10 c m hf
end ChainPrefix
