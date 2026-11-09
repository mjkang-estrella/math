import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH03_p (x : Points 5) : Points 5 := ([0, 4, 2, 1, 30, 5, 19, 12, 21, 27, 10, 9, 22, 16, 26, 15, 24, 7, 11, 29, 20, 14, 17, 6, 28, 25, 8, 18, 13, 23, 3] : List (Points 5)).getD x.val 0
def CollH03_pi (x : Points 5) : Points 5 := ([0, 3, 2, 30, 1, 5, 23, 17, 26, 11, 10, 18, 7, 28, 21, 15, 13, 22, 27, 6, 20, 8, 12, 29, 16, 25, 14, 9, 24, 19, 4] : List (Points 5)).getD x.val 0
def CollH03_l (x : Points 5) : Points 5 := ([3, 0, 2, 4, 1, 8, 5, 7, 9, 6, 13, 10, 12, 14, 11, 18, 15, 17, 19, 16, 23, 20, 22, 24, 21, 25, 27, 29, 26, 28, 30] : List (Points 5)).getD x.val 0
def CollH03_li (x : Points 5) : Points 5 := ([1, 4, 2, 0, 3, 6, 9, 7, 5, 8, 11, 14, 12, 10, 13, 16, 19, 17, 15, 18, 21, 24, 22, 20, 23, 25, 28, 26, 29, 27, 30] : List (Points 5)).getD x.val 0
def CollH03 : Collineation5 where
  p := CollH03_p
  pinv := CollH03_pi
  l := CollH03_l
  linv := CollH03_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
