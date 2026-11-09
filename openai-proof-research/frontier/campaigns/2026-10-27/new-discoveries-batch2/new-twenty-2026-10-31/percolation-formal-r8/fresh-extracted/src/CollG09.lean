import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG09_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 17, 10, 24, 27, 8, 21, 16, 25, 11, 6, 13, 26, 19, 20, 7, 29, 22, 14, 18, 5, 9, 15, 12, 23, 28, 1] : List (Points 5)).getD x.val 0
def CollG09_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 24, 14, 19, 9, 25, 6, 13, 27, 15, 22, 26, 11, 5, 23, 17, 18, 10, 21, 28, 7, 12, 16, 8, 29, 20, 4] : List (Points 5)).getD x.val 0
def CollG09_l (x : Points 5) : Points 5 := ([19, 20, 1, 7, 13, 24, 0, 6, 12, 18, 4, 5, 11, 17, 23, 9, 10, 16, 22, 3, 14, 15, 21, 2, 8, 25, 28, 29, 27, 30, 26] : List (Points 5)).getD x.val 0
def CollG09_li (x : Points 5) : Points 5 := ([6, 2, 23, 19, 10, 11, 7, 3, 24, 15, 16, 12, 8, 4, 20, 21, 17, 13, 9, 0, 1, 22, 18, 14, 5, 25, 30, 28, 26, 27, 29] : List (Points 5)).getD x.val 0
def CollG09 : Collineation5 where
  p := CollG09_p
  pinv := CollG09_pi
  l := CollG09_l
  linv := CollG09_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
