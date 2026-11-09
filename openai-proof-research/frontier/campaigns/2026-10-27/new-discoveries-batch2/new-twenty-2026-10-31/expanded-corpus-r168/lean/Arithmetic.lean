import Mathlib.Tactic
set_option maxHeartbeats 0
namespace SplitMatching381751
theorem local_arithmetic (a b c d e f g h i j k l : ℕ)
 (h0 : a+f+i ≤ 1) (h1 : a+e+j ≤ 1) (h2 : b+e+i ≤ 1)
 (h3 : b+f+k ≤ 1) (h4 : c+h+j ≤ 1) (h5 : c+g+l ≤ 1)
 (h6 : d+g+k ≤ 1) (h7 : d+h+l ≤ 1)
 (ha : a+b+c+d ≤ 1) (hb : e+f+g+h ≤ 3) (hc : i+j+k+l ≤ 3) :
 a+b+c+d+e+f+g+h+i+j+k+l ≤ 3 := by omega
end SplitMatching381751
