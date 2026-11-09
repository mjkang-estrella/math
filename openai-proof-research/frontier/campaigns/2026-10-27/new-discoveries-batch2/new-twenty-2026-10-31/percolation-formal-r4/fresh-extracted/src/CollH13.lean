import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH13_p (x : Points 5) : Points 5 := ([0, 9, 17, 21, 29, 5, 24, 2, 16, 28, 10, 14, 12, 11, 30, 15, 4, 22, 6, 27, 20, 19, 7, 1, 26, 25, 18, 3, 23, 8, 13] : List (Points 5)).getD x.val 0
def CollH13_pi (x : Points 5) : Points 5 := ([0, 23, 7, 27, 16, 5, 18, 22, 29, 1, 10, 13, 12, 30, 11, 15, 8, 2, 26, 21, 20, 3, 17, 28, 6, 25, 24, 19, 9, 4, 14] : List (Points 5)).getD x.val 0
def CollH13_l (x : Points 5) : Points 5 := ([3, 0, 2, 4, 1, 9, 6, 8, 5, 7, 10, 12, 14, 11, 13, 16, 18, 15, 17, 19, 22, 24, 21, 23, 20, 26, 28, 25, 27, 29, 30] : List (Points 5)).getD x.val 0
def CollH13_li (x : Points 5) : Points 5 := ([1, 4, 2, 0, 3, 8, 6, 9, 7, 5, 10, 13, 11, 14, 12, 17, 15, 18, 16, 19, 24, 22, 20, 23, 21, 27, 25, 28, 26, 29, 30] : List (Points 5)).getD x.val 0
def CollH13 : Collineation5 where
  p := CollH13_p
  pinv := CollH13_pi
  l := CollH13_l
  linv := CollH13_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
