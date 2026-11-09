import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG03_p (x : Points 5) : Points 5 := ([0, 15, 20, 10, 25, 4, 11, 17, 26, 23, 2, 24, 28, 16, 13, 1, 29, 14, 22, 18, 30, 7, 6, 9, 8, 3, 19, 21, 12, 27, 5] : List (Points 5)).getD x.val 0
def CollG03_pi (x : Points 5) : Points 5 := ([0, 15, 10, 25, 5, 30, 22, 21, 24, 23, 3, 6, 28, 14, 17, 1, 13, 7, 19, 26, 2, 27, 18, 9, 11, 4, 8, 29, 12, 16, 20] : List (Points 5)).getD x.val 0
def CollG03_l (x : Points 5) : Points 5 := ([23, 3, 8, 13, 18, 20, 0, 5, 10, 15, 22, 2, 7, 12, 17, 24, 4, 9, 14, 19, 21, 1, 6, 11, 16, 30, 27, 26, 29, 28, 25] : List (Points 5)).getD x.val 0
def CollG03_li (x : Points 5) : Points 5 := ([6, 21, 11, 1, 16, 7, 22, 12, 2, 17, 8, 23, 13, 3, 18, 9, 24, 14, 4, 19, 5, 20, 10, 0, 15, 30, 27, 26, 29, 28, 25] : List (Points 5)).getD x.val 0
def CollG03 : Collineation5 where
  p := CollG03_p
  pinv := CollG03_pi
  l := CollG03_l
  linv := CollG03_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
