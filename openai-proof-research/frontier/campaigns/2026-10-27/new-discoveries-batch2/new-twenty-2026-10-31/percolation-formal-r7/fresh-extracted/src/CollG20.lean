import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG20_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 10, 17, 8, 27, 24, 5, 14, 29, 18, 22, 15, 28, 12, 9, 23, 25, 6, 16, 11, 21, 20, 13, 19, 7, 26, 1] : List (Points 5)).getD x.val 0
def CollG20_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 10, 21, 28, 7, 18, 5, 23, 17, 26, 11, 15, 22, 6, 13, 27, 25, 24, 14, 19, 9, 20, 29, 8, 16, 12, 4] : List (Points 5)).getD x.val 0
def CollG20_l (x : Points 5) : Points 5 := ([9, 5, 6, 7, 8, 4, 0, 1, 2, 3, 24, 20, 21, 22, 23, 19, 15, 16, 17, 18, 14, 10, 11, 12, 13, 25, 29, 28, 27, 26, 30] : List (Points 5)).getD x.val 0
def CollG20_li (x : Points 5) : Points 5 := ([6, 7, 8, 9, 5, 1, 2, 3, 4, 0, 21, 22, 23, 24, 20, 16, 17, 18, 19, 15, 11, 12, 13, 14, 10, 25, 29, 28, 27, 26, 30] : List (Points 5)).getD x.val 0
def CollG20 : Collineation5 where
  p := CollG20_p
  pinv := CollG20_pi
  l := CollG20_l
  linv := CollG20_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
