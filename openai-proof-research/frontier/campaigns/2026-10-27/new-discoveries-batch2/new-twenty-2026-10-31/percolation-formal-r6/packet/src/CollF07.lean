import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF07_p (x : Points 5) : Points 5 := ([7, 19, 13, 20, 26, 16, 11, 21, 25, 6, 14, 22, 29, 5, 18, 23, 28, 9, 15, 12, 27, 8, 17, 10, 24, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF07_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 13, 9, 0, 21, 17, 23, 6, 19, 2, 10, 18, 5, 22, 14, 1, 3, 7, 11, 15, 24, 8, 4, 20, 16, 12, 29] : List (Points 5)).getD x.val 0
def CollF07_l (x : Points 5) : Points 5 := ([25, 29, 26, 30, 28, 14, 0, 16, 7, 23, 24, 17, 10, 8, 1, 19, 21, 3, 5, 12, 4, 13, 22, 6, 15, 9, 20, 11, 2, 18, 27] : List (Points 5)).getD x.val 0
def CollF07_li (x : Points 5) : Points 5 := ([6, 14, 28, 17, 20, 18, 23, 8, 13, 25, 12, 27, 19, 21, 5, 24, 7, 11, 29, 15, 26, 16, 22, 9, 10, 0, 2, 30, 4, 1, 3] : List (Points 5)).getD x.val 0
def CollF07 : Collineation5 where
  p := CollF07_p
  pinv := CollF07_pi
  l := CollF07_l
  linv := CollF07_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
