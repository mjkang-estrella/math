import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG06_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 18, 14, 22, 29, 5, 24, 17, 27, 10, 8, 12, 28, 15, 23, 9, 26, 20, 13, 19, 7, 6, 16, 11, 21, 25, 1] : List (Points 5)).getD x.val 0
def CollG06_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 9, 25, 24, 14, 19, 13, 27, 15, 22, 6, 17, 26, 11, 5, 23, 21, 28, 7, 18, 10, 29, 20, 12, 16, 8, 4] : List (Points 5)).getD x.val 0
def CollG06_l (x : Points 5) : Points 5 := ([4, 20, 16, 12, 8, 9, 0, 21, 17, 13, 14, 5, 1, 22, 18, 19, 10, 6, 2, 23, 24, 15, 11, 7, 3, 25, 30, 28, 26, 27, 29] : List (Points 5)).getD x.val 0
def CollG06_li (x : Points 5) : Points 5 := ([6, 12, 18, 24, 0, 11, 17, 23, 4, 5, 16, 22, 3, 9, 10, 21, 2, 8, 14, 15, 1, 7, 13, 19, 20, 25, 28, 29, 27, 30, 26] : List (Points 5)).getD x.val 0
def CollG06 : Collineation5 where
  p := CollG06_p
  pinv := CollG06_pi
  l := CollG06_l
  linv := CollG06_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
