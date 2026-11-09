import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF23_p (x : Points 5) : Points 5 := ([23, 12, 15, 9, 28, 14, 18, 5, 29, 22, 16, 6, 25, 21, 11, 7, 26, 20, 13, 19, 27, 24, 10, 17, 8, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF23_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 7, 11, 15, 24, 3, 22, 14, 1, 18, 5, 2, 10, 23, 6, 19, 17, 13, 9, 0, 21, 12, 16, 20, 4, 8, 29] : List (Points 5)).getD x.val 0
def CollF23_l (x : Points 5) : Points 5 := ([25, 28, 30, 26, 29, 14, 0, 16, 7, 23, 4, 22, 15, 13, 6, 9, 11, 18, 20, 2, 24, 8, 17, 1, 10, 19, 5, 21, 12, 3, 27] : List (Points 5)).getD x.val 0
def CollF23_li (x : Points 5) : Points 5 := ([6, 23, 19, 29, 10, 26, 14, 8, 21, 15, 24, 16, 28, 13, 5, 12, 7, 22, 17, 25, 18, 27, 11, 9, 20, 0, 3, 30, 1, 4, 2] : List (Points 5)).getD x.val 0
def CollF23 : Collineation5 where
  p := CollF23_p
  pinv := CollF23_pi
  l := CollF23_l
  linv := CollF23_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
