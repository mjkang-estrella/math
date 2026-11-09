import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF13_p (x : Points 5) : Points 5 := ([13, 7, 20, 19, 26, 9, 23, 15, 28, 12, 21, 16, 25, 11, 6, 17, 27, 10, 8, 24, 29, 14, 5, 22, 18, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF13_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 22, 14, 1, 18, 5, 17, 13, 9, 0, 21, 7, 11, 15, 24, 3, 2, 10, 23, 6, 19, 12, 4, 16, 8, 20, 29] : List (Points 5)).getD x.val 0
def CollF13_l (x : Points 5) : Points 5 := ([25, 29, 30, 28, 27, 24, 0, 6, 12, 18, 4, 17, 5, 23, 11, 14, 21, 8, 15, 2, 19, 13, 7, 1, 20, 9, 10, 16, 22, 3, 26] : List (Points 5)).getD x.val 0
def CollF13_li (x : Points 5) : Points 5 := ([6, 23, 19, 29, 10, 12, 7, 22, 17, 25, 26, 14, 8, 21, 15, 18, 27, 11, 9, 20, 24, 16, 28, 13, 5, 0, 30, 4, 3, 1, 2] : List (Points 5)).getD x.val 0
def CollF13 : Collineation5 where
  p := CollF13_p
  pinv := CollF13_pi
  l := CollF13_l
  linv := CollF13_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
