import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF21_p (x : Points 5) : Points 5 := ([21, 11, 16, 6, 25, 13, 19, 7, 26, 20, 17, 8, 27, 24, 10, 9, 28, 23, 12, 15, 29, 22, 14, 18, 5, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF21_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 24, 3, 7, 11, 15, 14, 1, 18, 5, 22, 19, 2, 10, 23, 6, 9, 0, 21, 17, 13, 4, 8, 12, 16, 20, 29] : List (Points 5)).getD x.val 0
def CollF21_l (x : Points 5) : Points 5 := ([25, 30, 27, 29, 28, 24, 0, 6, 12, 18, 14, 2, 15, 8, 21, 19, 1, 13, 20, 7, 9, 3, 22, 16, 10, 4, 5, 11, 17, 23, 26] : List (Points 5)).getD x.val 0
def CollF21_li (x : Points 5) : Points 5 := ([6, 16, 11, 21, 25, 26, 7, 19, 13, 20, 24, 27, 8, 17, 10, 12, 23, 28, 9, 15, 18, 14, 22, 29, 5, 0, 30, 2, 4, 3, 1] : List (Points 5)).getD x.val 0
def CollF21 : Collineation5 where
  p := CollF21_p
  pinv := CollF21_pi
  l := CollF21_l
  linv := CollF21_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
