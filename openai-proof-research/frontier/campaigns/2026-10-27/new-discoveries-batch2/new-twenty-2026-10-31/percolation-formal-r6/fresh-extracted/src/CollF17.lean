import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF17_p (x : Points 5) : Points 5 := ([17, 24, 8, 10, 27, 21, 6, 11, 25, 16, 9, 12, 28, 15, 23, 13, 26, 19, 20, 7, 29, 18, 22, 5, 14, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF17_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 23, 6, 19, 2, 10, 3, 7, 11, 15, 24, 13, 9, 0, 21, 17, 18, 5, 22, 14, 1, 8, 16, 4, 12, 20, 29] : List (Points 5)).getD x.val 0
def CollF17_l (x : Points 5) : Points 5 := ([25, 27, 28, 30, 29, 24, 0, 6, 12, 18, 19, 7, 20, 13, 1, 9, 16, 3, 10, 22, 4, 23, 17, 11, 5, 14, 15, 21, 2, 8, 26] : List (Points 5)).getD x.val 0
def CollF17_li (x : Points 5) : Points 5 := ([6, 14, 28, 17, 20, 24, 7, 11, 29, 15, 18, 23, 8, 13, 25, 26, 16, 22, 9, 10, 12, 27, 19, 21, 5, 0, 30, 1, 2, 4, 3] : List (Points 5)).getD x.val 0
def CollF17 : Collineation5 where
  p := CollF17_p
  pinv := CollF17_pi
  l := CollF17_l
  linv := CollF17_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
