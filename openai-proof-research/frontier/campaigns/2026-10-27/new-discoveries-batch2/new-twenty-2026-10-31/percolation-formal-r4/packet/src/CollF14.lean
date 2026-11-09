import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF14_p (x : Points 5) : Points 5 := ([14, 5, 22, 18, 29, 7, 20, 19, 26, 13, 23, 15, 28, 12, 9, 16, 25, 11, 6, 21, 27, 10, 8, 24, 17, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF14_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 1, 18, 5, 22, 14, 21, 17, 13, 9, 0, 11, 15, 24, 3, 7, 6, 19, 2, 10, 23, 16, 8, 20, 12, 4, 29] : List (Points 5)).getD x.val 0
def CollF14_l (x : Points 5) : Points 5 := ([25, 26, 28, 29, 30, 14, 0, 16, 7, 23, 19, 12, 5, 3, 21, 4, 6, 13, 15, 22, 9, 18, 2, 11, 20, 24, 10, 1, 17, 8, 27] : List (Points 5)).getD x.val 0
def CollF14_li (x : Points 5) : Points 5 := ([6, 27, 22, 13, 15, 12, 16, 8, 29, 20, 26, 23, 11, 17, 5, 18, 7, 28, 21, 10, 24, 14, 19, 9, 25, 0, 1, 30, 2, 3, 4] : List (Points 5)).getD x.val 0
def CollF14 : Collineation5 where
  p := CollF14_p
  pinv := CollF14_pi
  l := CollF14_l
  linv := CollF14_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
