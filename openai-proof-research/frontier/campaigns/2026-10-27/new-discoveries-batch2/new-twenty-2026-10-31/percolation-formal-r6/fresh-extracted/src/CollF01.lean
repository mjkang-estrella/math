import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF01_p (x : Points 5) : Points 5 := ([1, 18, 22, 14, 29, 3, 12, 19, 27, 21, 2, 24, 28, 16, 13, 4, 26, 11, 23, 17, 30, 6, 8, 7, 9, 0, 15, 20, 10, 25, 5] : List (Points 5)).getD x.val 0
def CollF01_pi (x : Points 5) : Points 5 := ([25, 0, 10, 5, 15, 30, 21, 23, 22, 24, 28, 17, 6, 14, 3, 26, 13, 19, 1, 7, 27, 9, 2, 18, 11, 29, 16, 8, 12, 4, 20] : List (Points 5)).getD x.val 0
def CollF01_l (x : Points 5) : Points 5 := ([30, 26, 28, 27, 29, 20, 0, 5, 10, 15, 22, 12, 2, 17, 7, 21, 6, 16, 1, 11, 23, 18, 13, 8, 3, 24, 4, 9, 14, 19, 25] : List (Points 5)).getD x.val 0
def CollF01_li (x : Points 5) : Points 5 := ([6, 18, 12, 24, 26, 7, 16, 14, 23, 27, 8, 19, 11, 22, 28, 9, 17, 13, 21, 29, 5, 15, 10, 20, 25, 30, 1, 3, 2, 4, 0] : List (Points 5)).getD x.val 0
def CollF01 : Collineation5 where
  p := CollF01_p
  pinv := CollF01_pi
  l := CollF01_l
  linv := CollF01_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
