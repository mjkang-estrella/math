import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG15_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 20, 7, 13, 26, 19, 10, 24, 27, 8, 17, 5, 29, 22, 14, 18, 25, 11, 6, 21, 16, 15, 23, 9, 12, 28, 1] : List (Points 5)).getD x.val 0
def CollG15_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 15, 22, 6, 13, 27, 10, 21, 28, 7, 18, 25, 24, 14, 19, 9, 5, 23, 17, 26, 11, 20, 8, 12, 29, 16, 4] : List (Points 5)).getD x.val 0
def CollG15_l (x : Points 5) : Points 5 := ([19, 15, 16, 17, 18, 4, 0, 1, 2, 3, 14, 10, 11, 12, 13, 24, 20, 21, 22, 23, 9, 5, 6, 7, 8, 25, 28, 26, 29, 27, 30] : List (Points 5)).getD x.val 0
def CollG15_li (x : Points 5) : Points 5 := ([6, 7, 8, 9, 5, 21, 22, 23, 24, 20, 11, 12, 13, 14, 10, 1, 2, 3, 4, 0, 16, 17, 18, 19, 15, 25, 27, 29, 26, 28, 30] : List (Points 5)).getD x.val 0
def CollG15 : Collineation5 where
  p := CollG15_p
  pinv := CollG15_pi
  l := CollG15_l
  linv := CollG15_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
