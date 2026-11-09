import ChainFirst6_9_0
import ChainFirst6_9_1
import ChainFirst6_9_2
import ChainFirst6_9_3
import ChainFirst6_9_4
import ChainFirst6_9_5
import ChainFirst6_9_6
import ChainFirst6_9_7
import ChainFirst6_9_8
import ChainFirst6_9_9
import ChainFirst6_9_10
namespace ChainPrefix
theorem case6_9 (b c m : V) (hf : Fits (first 6 b c 9 m)) : ((b = 1 ∧ c = 8) ∨ (b = 8 ∧ c = 1)) ∧ ((9:V) = 3 ∧ m = 4 ∨ 9 = 4 ∧ m = 3) := by
  fin_cases b
  · exact case6_9_0 c m hf
  · exact case6_9_1 c m hf
  · exact case6_9_2 c m hf
  · exact case6_9_3 c m hf
  · exact case6_9_4 c m hf
  · exact case6_9_5 c m hf
  · exact case6_9_6 c m hf
  · exact case6_9_7 c m hf
  · exact case6_9_8 c m hf
  · exact case6_9_9 c m hf
  · exact case6_9_10 c m hf
end ChainPrefix
