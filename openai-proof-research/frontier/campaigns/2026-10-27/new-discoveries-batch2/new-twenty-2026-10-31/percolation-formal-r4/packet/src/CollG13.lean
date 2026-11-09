import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG13_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 9, 23, 15, 28, 12, 17, 8, 27, 24, 10, 21, 25, 6, 16, 11, 29, 18, 22, 5, 14, 13, 7, 20, 19, 26, 1] : List (Points 5)).getD x.val 0
def CollG13_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 23, 17, 26, 11, 5, 14, 19, 9, 25, 24, 7, 18, 10, 21, 28, 27, 15, 22, 6, 13, 16, 29, 12, 8, 20, 4] : List (Points 5)).getD x.val 0
def CollG13_l (x : Points 5) : Points 5 := ([9, 10, 16, 22, 3, 24, 0, 6, 12, 18, 14, 15, 21, 2, 8, 4, 5, 11, 17, 23, 19, 20, 1, 7, 13, 25, 29, 30, 28, 27, 26] : List (Points 5)).getD x.val 0
def CollG13_li (x : Points 5) : Points 5 := ([6, 22, 13, 4, 15, 16, 7, 23, 14, 0, 1, 17, 8, 24, 10, 11, 2, 18, 9, 20, 21, 12, 3, 19, 5, 25, 30, 29, 28, 26, 27] : List (Points 5)).getD x.val 0
def CollG13 : Collineation5 where
  p := CollG13_p
  pinv := CollG13_pi
  l := CollG13_l
  linv := CollG13_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
