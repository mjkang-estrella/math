import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF29_p (x : Points 5) : Points 5 := ([29, 5, 18, 14, 22, 9, 15, 12, 23, 28, 17, 10, 24, 27, 8, 13, 20, 26, 7, 19, 21, 25, 6, 16, 11, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF29_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 1, 22, 18, 14, 5, 11, 24, 7, 15, 3, 6, 23, 10, 2, 19, 16, 20, 4, 8, 12, 21, 17, 13, 9, 0, 29] : List (Points 5)).getD x.val 0
def CollF29_l (x : Points 5) : Points 5 := ([25, 28, 29, 27, 30, 4, 5, 11, 17, 23, 14, 2, 15, 8, 21, 9, 16, 3, 10, 22, 19, 13, 7, 1, 20, 24, 0, 6, 12, 18, 26] : List (Points 5)).getD x.val 0
def CollF29_li (x : Points 5) : Points 5 := ([26, 23, 11, 17, 5, 6, 27, 22, 13, 15, 18, 7, 28, 21, 10, 12, 16, 8, 29, 20, 24, 14, 19, 9, 25, 0, 30, 3, 1, 2, 4] : List (Points 5)).getD x.val 0
def CollF29 : Collineation5 where
  p := CollF29_p
  pinv := CollF29_pi
  l := CollF29_l
  linv := CollF29_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
