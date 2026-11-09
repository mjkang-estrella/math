import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF19_p (x : Points 5) : Points 5 := ([19, 20, 7, 13, 26, 22, 5, 14, 29, 18, 8, 10, 27, 17, 24, 11, 25, 16, 21, 6, 28, 15, 23, 9, 12, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF19_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 6, 19, 2, 10, 23, 11, 15, 24, 3, 7, 21, 17, 13, 9, 0, 1, 18, 5, 22, 14, 16, 4, 12, 20, 8, 29] : List (Points 5)).getD x.val 0
def CollF19_l (x : Points 5) : Points 5 := ([25, 29, 27, 26, 30, 19, 0, 11, 22, 8, 14, 17, 20, 3, 6, 4, 21, 18, 10, 7, 24, 13, 2, 16, 5, 9, 15, 1, 12, 23, 28] : List (Points 5)).getD x.val 0
def CollF19_li (x : Points 5) : Points 5 := ([6, 27, 22, 13, 15, 24, 14, 19, 9, 25, 18, 7, 28, 21, 10, 26, 23, 11, 17, 5, 12, 16, 8, 29, 20, 0, 3, 2, 30, 1, 4] : List (Points 5)).getD x.val 0
def CollF19 : Collineation5 where
  p := CollF19_p
  pinv := CollF19_pi
  l := CollF19_l
  linv := CollF19_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
