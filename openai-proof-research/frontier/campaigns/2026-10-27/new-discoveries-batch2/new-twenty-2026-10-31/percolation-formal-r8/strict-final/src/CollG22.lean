import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG22_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 11, 16, 6, 25, 21, 8, 10, 27, 17, 24, 19, 26, 13, 7, 20, 28, 9, 15, 12, 23, 22, 14, 18, 5, 29, 1] : List (Points 5)).getD x.val 0
def CollG22_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 28, 7, 18, 10, 21, 11, 5, 23, 17, 26, 22, 6, 13, 27, 15, 19, 9, 25, 24, 14, 8, 16, 12, 20, 29, 4] : List (Points 5)).getD x.val 0
def CollG22_l (x : Points 5) : Points 5 := ([24, 5, 16, 2, 13, 19, 0, 11, 22, 8, 14, 20, 6, 17, 3, 9, 15, 1, 12, 23, 4, 10, 21, 7, 18, 25, 26, 29, 30, 27, 28] : List (Points 5)).getD x.val 0
def CollG22_li (x : Points 5) : Points 5 := ([6, 17, 3, 14, 20, 1, 12, 23, 9, 15, 21, 7, 18, 4, 10, 16, 2, 13, 24, 5, 11, 22, 8, 19, 0, 25, 26, 29, 30, 27, 28] : List (Points 5)).getD x.val 0
def CollG22 : Collineation5 where
  p := CollG22_p
  pinv := CollG22_pi
  l := CollG22_l
  linv := CollG22_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
