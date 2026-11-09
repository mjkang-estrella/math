import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF20_p (x : Points 5) : Points 5 := ([20, 13, 19, 7, 26, 10, 17, 8, 27, 24, 15, 9, 28, 23, 12, 5, 29, 22, 14, 18, 25, 21, 11, 16, 6, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF20_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 15, 24, 3, 7, 11, 5, 22, 14, 1, 18, 10, 23, 6, 19, 2, 0, 21, 17, 13, 9, 20, 4, 8, 12, 16, 29] : List (Points 5)).getD x.val 0
def CollF20_l (x : Points 5) : Points 5 := ([25, 29, 28, 27, 26, 4, 0, 1, 2, 3, 19, 17, 15, 18, 16, 24, 21, 23, 20, 22, 14, 13, 12, 11, 10, 9, 5, 6, 7, 8, 30] : List (Points 5)).getD x.val 0
def CollF20_li (x : Points 5) : Points 5 := ([6, 7, 8, 9, 5, 26, 27, 28, 29, 25, 24, 23, 22, 21, 20, 12, 14, 11, 13, 10, 18, 16, 19, 17, 15, 0, 4, 3, 2, 1, 30] : List (Points 5)).getD x.val 0
def CollF20 : Collineation5 where
  p := CollF20_p
  pinv := CollF20_pi
  l := CollF20_l
  linv := CollF20_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
