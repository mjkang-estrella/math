import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH09_p (x : Points 5) : Points 5 := ([0, 17, 21, 13, 29, 5, 7, 6, 8, 30, 10, 22, 16, 3, 26, 15, 12, 1, 23, 28, 20, 2, 11, 18, 27, 25, 14, 24, 19, 4, 9] : List (Points 5)).getD x.val 0
def CollH09_pi (x : Points 5) : Points 5 := ([0, 17, 21, 13, 29, 5, 7, 6, 8, 30, 10, 22, 16, 3, 26, 15, 12, 1, 23, 28, 20, 2, 11, 18, 27, 25, 14, 24, 19, 4, 9] : List (Points 5)).getD x.val 0
def CollH09_l (x : Points 5) : Points 5 := ([1, 0, 4, 3, 2, 7, 6, 5, 9, 8, 13, 12, 11, 10, 14, 19, 18, 17, 16, 15, 20, 24, 23, 22, 21, 26, 25, 29, 28, 27, 30] : List (Points 5)).getD x.val 0
def CollH09_li (x : Points 5) : Points 5 := ([1, 0, 4, 3, 2, 7, 6, 5, 9, 8, 13, 12, 11, 10, 14, 19, 18, 17, 16, 15, 20, 24, 23, 22, 21, 26, 25, 29, 28, 27, 30] : List (Points 5)).getD x.val 0
def CollH09 : Collineation5 where
  p := CollH09_p
  pinv := CollH09_pi
  l := CollH09_l
  linv := CollH09_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
