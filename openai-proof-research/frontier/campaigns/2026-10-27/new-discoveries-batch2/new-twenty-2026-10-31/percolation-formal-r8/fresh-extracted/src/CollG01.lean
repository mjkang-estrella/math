import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG01_p (x : Points 5) : Points 5 := ([0, 15, 20, 10, 25, 3, 12, 19, 27, 21, 4, 23, 26, 17, 11, 2, 28, 13, 24, 16, 30, 9, 7, 8, 6, 1, 18, 22, 14, 29, 5] : List (Points 5)).getD x.val 0
def CollG01_pi (x : Points 5) : Points 5 := ([0, 25, 15, 5, 10, 30, 24, 22, 23, 21, 3, 14, 6, 17, 28, 1, 19, 13, 26, 7, 2, 9, 27, 11, 18, 4, 12, 8, 16, 29, 20] : List (Points 5)).getD x.val 0
def CollG01_l (x : Points 5) : Points 5 := ([24, 4, 9, 14, 19, 20, 0, 5, 10, 15, 21, 1, 6, 11, 16, 22, 2, 7, 12, 17, 23, 3, 8, 13, 18, 30, 26, 28, 27, 29, 25] : List (Points 5)).getD x.val 0
def CollG01_li (x : Points 5) : Points 5 := ([6, 11, 16, 21, 1, 7, 12, 17, 22, 2, 8, 13, 18, 23, 3, 9, 14, 19, 24, 4, 5, 10, 15, 20, 0, 30, 26, 28, 27, 29, 25] : List (Points 5)).getD x.val 0
def CollG01 : Collineation5 where
  p := CollG01_p
  pinv := CollG01_pi
  l := CollG01_l
  linv := CollG01_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
