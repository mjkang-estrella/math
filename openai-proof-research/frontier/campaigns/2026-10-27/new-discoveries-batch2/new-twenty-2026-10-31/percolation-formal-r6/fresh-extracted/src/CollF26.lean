import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF26_p (x : Points 5) : Points 5 := ([26, 7, 19, 13, 20, 6, 16, 11, 21, 25, 18, 14, 22, 29, 5, 12, 23, 28, 9, 15, 24, 27, 8, 17, 10, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF26_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 14, 5, 1, 22, 18, 24, 7, 15, 3, 11, 19, 6, 23, 10, 2, 4, 8, 12, 16, 20, 9, 0, 21, 17, 13, 29] : List (Points 5)).getD x.val 0
def CollF26_l (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 14, 5, 1, 22, 18, 24, 7, 15, 3, 11, 19, 6, 23, 10, 2, 4, 8, 12, 16, 20, 9, 0, 21, 17, 13, 29] : List (Points 5)).getD x.val 0
def CollF26_li (x : Points 5) : Points 5 := ([26, 7, 19, 13, 20, 6, 16, 11, 21, 25, 18, 14, 22, 29, 5, 12, 23, 28, 9, 15, 24, 27, 8, 17, 10, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF26 : Collineation5 where
  p := CollF26_p
  pinv := CollF26_pi
  l := CollF26_l
  linv := CollF26_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
