import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF06_p (x : Points 5) : Points 5 := ([6, 16, 11, 21, 25, 18, 14, 22, 29, 5, 12, 23, 28, 9, 15, 24, 27, 8, 17, 10, 26, 7, 19, 13, 20, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF06_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 9, 0, 21, 17, 13, 19, 2, 10, 23, 6, 14, 1, 18, 5, 22, 24, 3, 7, 11, 15, 4, 20, 16, 12, 8, 29] : List (Points 5)).getD x.val 0
def CollF06_l (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 9, 0, 21, 17, 13, 19, 2, 10, 23, 6, 14, 1, 18, 5, 22, 24, 3, 7, 11, 15, 4, 20, 16, 12, 8, 29] : List (Points 5)).getD x.val 0
def CollF06_li (x : Points 5) : Points 5 := ([6, 16, 11, 21, 25, 18, 14, 22, 29, 5, 12, 23, 28, 9, 15, 24, 27, 8, 17, 10, 26, 7, 19, 13, 20, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF06 : Collineation5 where
  p := CollF06_p
  pinv := CollF06_pi
  l := CollF06_l
  linv := CollF06_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
