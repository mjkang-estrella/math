import ChainFirst6_7_0
import ChainFirst6_7_1
import ChainFirst6_7_2
import ChainFirst6_7_3
import ChainFirst6_7_4
import ChainFirst6_7_5
import ChainFirst6_7_6
import ChainFirst6_7_7
import ChainFirst6_7_8
import ChainFirst6_7_9
import ChainFirst6_7_10
namespace ChainPrefix
theorem case6_7 (b c m : V) (hf : Fits (first 6 b c 7 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((7:V) = 3 ∧ m = 4 ∨ 7 = 4 ∧ m = 3) := by
  fin_cases b
  · exact case6_7_0 c m hf
  · exact case6_7_1 c m hf
  · exact case6_7_2 c m hf
  · exact case6_7_3 c m hf
  · exact case6_7_4 c m hf
  · exact case6_7_5 c m hf
  · exact case6_7_6 c m hf
  · exact case6_7_7 c m hf
  · exact case6_7_8 c m hf
  · exact case6_7_9 c m hf
  · exact case6_7_10 c m hf
end ChainPrefix
