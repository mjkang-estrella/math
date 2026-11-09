import ChainFirst6_6_0
import ChainFirst6_6_1
import ChainFirst6_6_2
import ChainFirst6_6_3
import ChainFirst6_6_4
import ChainFirst6_6_5
import ChainFirst6_6_6
import ChainFirst6_6_7
import ChainFirst6_6_8
import ChainFirst6_6_9
import ChainFirst6_6_10
namespace ChainPrefix
theorem case6_6 (b c m : V) (hf : Fits (first 6 b c 6 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((6:V) = 3 ∧ m = 4 ∨ 6 = 4 ∧ m = 3) := by
  fin_cases b
  · exact case6_6_0 c m hf
  · exact case6_6_1 c m hf
  · exact case6_6_2 c m hf
  · exact case6_6_3 c m hf
  · exact case6_6_4 c m hf
  · exact case6_6_5 c m hf
  · exact case6_6_6 c m hf
  · exact case6_6_7 c m hf
  · exact case6_6_8 c m hf
  · exact case6_6_9 c m hf
  · exact case6_6_10 c m hf
end ChainPrefix
