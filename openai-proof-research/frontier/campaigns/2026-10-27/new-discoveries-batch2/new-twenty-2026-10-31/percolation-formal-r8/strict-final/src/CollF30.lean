import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF30_p (x : Points 5) : Points 5 := ([30, 6, 8, 7, 9, 1, 18, 22, 14, 29, 3, 12, 19, 27, 21, 2, 24, 28, 16, 13, 4, 26, 11, 23, 17, 0, 15, 20, 10, 25, 5] : List (Points 5)).getD x.val 0
def CollF30_pi (x : Points 5) : Points 5 := ([25, 5, 15, 10, 20, 30, 1, 3, 2, 4, 28, 22, 11, 19, 8, 26, 18, 24, 6, 12, 27, 14, 7, 23, 16, 29, 21, 13, 17, 9, 0] : List (Points 5)).getD x.val 0
def CollF30_l (x : Points 5) : Points 5 := ([30, 26, 28, 27, 29, 21, 1, 6, 11, 16, 23, 13, 3, 18, 8, 22, 7, 17, 2, 12, 24, 19, 14, 9, 4, 20, 0, 5, 10, 15, 25] : List (Points 5)).getD x.val 0
def CollF30_li (x : Points 5) : Points 5 := ([26, 6, 18, 12, 24, 27, 7, 16, 14, 23, 28, 8, 19, 11, 22, 29, 9, 17, 13, 21, 25, 5, 15, 10, 20, 30, 1, 3, 2, 4, 0] : List (Points 5)).getD x.val 0
def CollF30 : Collineation5 where
  p := CollF30_p
  pinv := CollF30_pi
  l := CollF30_l
  linv := CollF30_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
