import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF15_p (x : Points 5) : Points 5 := ([15, 23, 9, 12, 28, 20, 7, 13, 26, 19, 5, 14, 29, 18, 22, 10, 27, 17, 24, 8, 25, 16, 21, 6, 11, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF15_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 10, 23, 6, 19, 2, 15, 24, 3, 7, 11, 0, 21, 17, 13, 9, 5, 22, 14, 1, 18, 20, 8, 16, 4, 12, 29] : List (Points 5)).getD x.val 0
def CollF15_l (x : Points 5) : Points 5 := ([25, 28, 26, 29, 27, 4, 0, 1, 2, 3, 24, 22, 20, 23, 21, 14, 11, 13, 10, 12, 9, 8, 7, 6, 5, 19, 15, 16, 17, 18, 30] : List (Points 5)).getD x.val 0
def CollF15_li (x : Points 5) : Points 5 := ([6, 7, 8, 9, 5, 24, 23, 22, 21, 20, 18, 16, 19, 17, 15, 26, 27, 28, 29, 25, 12, 14, 11, 13, 10, 0, 2, 4, 1, 3, 30] : List (Points 5)).getD x.val 0
def CollF15 : Collineation5 where
  p := CollF15_p
  pinv := CollF15_pi
  l := CollF15_l
  linv := CollF15_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
