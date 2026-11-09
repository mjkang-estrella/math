import ChainFirst6_5_0
import ChainFirst6_5_1
import ChainFirst6_5_2
import ChainFirst6_5_3
import ChainFirst6_5_4
import ChainFirst6_5_5
import ChainFirst6_5_6
import ChainFirst6_5_7
import ChainFirst6_5_8
import ChainFirst6_5_9
import ChainFirst6_5_10
namespace ChainPrefix
theorem case6_5 (b c m : V) (hf : Fits (first 6 b c 5 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((5:V) = 3 ∧ m = 4 ∨ 5 = 4 ∧ m = 3) := by
  fin_cases b
  · exact case6_5_0 c m hf
  · exact case6_5_1 c m hf
  · exact case6_5_2 c m hf
  · exact case6_5_3 c m hf
  · exact case6_5_4 c m hf
  · exact case6_5_5 c m hf
  · exact case6_5_6 c m hf
  · exact case6_5_7 c m hf
  · exact case6_5_8 c m hf
  · exact case6_5_9 c m hf
  · exact case6_5_10 c m hf
end ChainPrefix
