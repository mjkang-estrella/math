import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF02_p (x : Points 5) : Points 5 := ([2, 16, 24, 13, 28, 1, 14, 18, 29, 22, 4, 23, 26, 17, 11, 3, 27, 12, 21, 19, 30, 7, 6, 9, 8, 0, 15, 20, 10, 25, 5] : List (Points 5)).getD x.val 0
def CollF02_pi (x : Points 5) : Points 5 := ([25, 5, 0, 15, 10, 30, 22, 21, 24, 23, 28, 14, 17, 3, 6, 26, 1, 13, 7, 19, 27, 18, 9, 11, 2, 29, 12, 16, 4, 8, 20] : List (Points 5)).getD x.val 0
def CollF02_l (x : Points 5) : Points 5 := ([30, 28, 29, 26, 27, 20, 0, 5, 10, 15, 21, 11, 1, 16, 6, 23, 8, 18, 3, 13, 24, 19, 14, 9, 4, 22, 2, 7, 12, 17, 25] : List (Points 5)).getD x.val 0
def CollF02_li (x : Points 5) : Points 5 := ([6, 12, 26, 18, 24, 7, 14, 27, 16, 23, 8, 11, 28, 19, 22, 9, 13, 29, 17, 21, 5, 10, 25, 15, 20, 30, 3, 4, 1, 2, 0] : List (Points 5)).getD x.val 0
def CollF02 : Collineation5 where
  p := CollF02_p
  pinv := CollF02_pi
  l := CollF02_l
  linv := CollF02_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
