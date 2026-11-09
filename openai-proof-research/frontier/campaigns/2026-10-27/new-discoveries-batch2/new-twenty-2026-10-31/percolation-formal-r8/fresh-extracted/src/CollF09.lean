import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF09_p (x : Points 5) : Points 5 := ([9, 15, 12, 23, 28, 17, 10, 24, 27, 8, 13, 20, 26, 7, 19, 21, 25, 6, 16, 11, 29, 5, 18, 14, 22, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF09_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 21, 17, 13, 9, 0, 6, 19, 2, 10, 23, 1, 18, 5, 22, 14, 11, 15, 24, 3, 7, 16, 12, 8, 4, 20, 29] : List (Points 5)).getD x.val 0
def CollF09_l (x : Points 5) : Points 5 := ([25, 28, 29, 27, 30, 24, 0, 6, 12, 18, 9, 22, 10, 3, 16, 4, 11, 23, 5, 17, 14, 8, 2, 21, 15, 19, 20, 1, 7, 13, 26] : List (Points 5)).getD x.val 0
def CollF09_li (x : Points 5) : Points 5 := ([6, 27, 22, 13, 15, 18, 7, 28, 21, 10, 12, 16, 8, 29, 20, 24, 14, 19, 9, 25, 26, 23, 11, 17, 5, 0, 30, 3, 1, 2, 4] : List (Points 5)).getD x.val 0
def CollF09 : Collineation5 where
  p := CollF09_p
  pinv := CollF09_pi
  l := CollF09_l
  linv := CollF09_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
