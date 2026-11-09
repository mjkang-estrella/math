import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG29_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 9, 15, 12, 23, 28, 13, 7, 20, 19, 26, 17, 24, 8, 10, 27, 21, 11, 16, 6, 25, 29, 5, 18, 14, 22, 1] : List (Points 5)).getD x.val 0
def CollG29_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 26, 23, 11, 17, 5, 18, 21, 7, 10, 28, 6, 22, 15, 27, 13, 12, 20, 29, 8, 16, 24, 14, 19, 9, 25, 4] : List (Points 5)).getD x.val 0
def CollG29_l (x : Points 5) : Points 5 := ([24, 0, 6, 12, 18, 4, 5, 11, 17, 23, 9, 10, 16, 22, 3, 14, 15, 21, 2, 8, 19, 20, 1, 7, 13, 25, 28, 29, 27, 30, 26] : List (Points 5)).getD x.val 0
def CollG29_li (x : Points 5) : Points 5 := ([1, 22, 18, 14, 5, 6, 2, 23, 19, 10, 11, 7, 3, 24, 15, 16, 12, 8, 4, 20, 21, 17, 13, 9, 0, 25, 30, 28, 26, 27, 29] : List (Points 5)).getD x.val 0
def CollG29 : Collineation5 where
  p := CollG29_p
  pinv := CollG29_pi
  l := CollG29_l
  linv := CollG29_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
