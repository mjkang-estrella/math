import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG14_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 7, 20, 19, 26, 13, 16, 6, 25, 21, 11, 23, 28, 9, 15, 12, 27, 17, 24, 8, 10, 14, 5, 22, 18, 29, 1] : List (Points 5)).getD x.val 0
def CollG14_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 26, 11, 5, 23, 17, 24, 14, 19, 9, 25, 18, 10, 21, 28, 7, 6, 13, 27, 15, 22, 12, 8, 20, 16, 29, 4] : List (Points 5)).getD x.val 0
def CollG14_l (x : Points 5) : Points 5 := ([24, 10, 1, 17, 8, 14, 0, 16, 7, 23, 4, 15, 6, 22, 13, 19, 5, 21, 12, 3, 9, 20, 11, 2, 18, 25, 26, 28, 29, 30, 27] : List (Points 5)).getD x.val 0
def CollG14_li (x : Points 5) : Points 5 := ([6, 2, 23, 19, 10, 16, 12, 8, 4, 20, 1, 22, 18, 14, 5, 11, 7, 3, 24, 15, 21, 17, 13, 9, 0, 25, 26, 30, 27, 28, 29] : List (Points 5)).getD x.val 0
def CollG14 : Collineation5 where
  p := CollG14_p
  pinv := CollG14_pi
  l := CollG14_l
  linv := CollG14_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
