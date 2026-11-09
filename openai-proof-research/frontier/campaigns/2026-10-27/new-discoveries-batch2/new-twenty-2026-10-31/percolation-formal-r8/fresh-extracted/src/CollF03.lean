import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF03_p (x : Points 5) : Points 5 := ([3, 19, 21, 12, 27, 4, 11, 17, 26, 23, 1, 22, 29, 18, 14, 2, 28, 13, 24, 16, 30, 8, 9, 6, 7, 0, 15, 20, 10, 25, 5] : List (Points 5)).getD x.val 0
def CollF03_pi (x : Points 5) : Points 5 := ([25, 10, 15, 0, 5, 30, 23, 24, 21, 22, 28, 6, 3, 17, 14, 26, 19, 7, 13, 1, 27, 2, 11, 9, 18, 29, 8, 4, 16, 12, 20] : List (Points 5)).getD x.val 0
def CollF03_l (x : Points 5) : Points 5 := ([30, 27, 26, 29, 28, 20, 0, 5, 10, 15, 24, 14, 4, 19, 9, 22, 7, 17, 2, 12, 21, 16, 11, 6, 1, 23, 3, 8, 13, 18, 25] : List (Points 5)).getD x.val 0
def CollF03_li (x : Points 5) : Points 5 := ([6, 24, 18, 26, 12, 7, 23, 16, 27, 14, 8, 22, 19, 28, 11, 9, 21, 17, 29, 13, 5, 20, 15, 25, 10, 30, 2, 1, 4, 3, 0] : List (Points 5)).getD x.val 0
def CollF03 : Collineation5 where
  p := CollF03_p
  pinv := CollF03_pi
  l := CollF03_l
  linv := CollF03_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
