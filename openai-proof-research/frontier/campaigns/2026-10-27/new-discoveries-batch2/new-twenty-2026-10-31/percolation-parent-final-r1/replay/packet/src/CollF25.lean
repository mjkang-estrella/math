import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF25_p (x : Points 5) : Points 5 := ([25, 6, 16, 11, 21, 5, 18, 14, 22, 29, 15, 12, 23, 28, 9, 10, 24, 27, 8, 17, 20, 26, 7, 19, 13, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF25_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 5, 1, 22, 18, 14, 15, 3, 11, 24, 7, 10, 2, 19, 6, 23, 20, 4, 8, 12, 16, 0, 21, 17, 13, 9, 29] : List (Points 5)).getD x.val 0
def CollF25_l (x : Points 5) : Points 5 := ([25, 26, 27, 28, 29, 9, 5, 6, 7, 8, 19, 17, 15, 18, 16, 14, 11, 13, 10, 12, 24, 23, 22, 21, 20, 4, 0, 1, 2, 3, 30] : List (Points 5)).getD x.val 0
def CollF25_li (x : Points 5) : Points 5 := ([26, 27, 28, 29, 25, 6, 7, 8, 9, 5, 18, 16, 19, 17, 15, 12, 14, 11, 13, 10, 24, 23, 22, 21, 20, 0, 1, 2, 3, 4, 30] : List (Points 5)).getD x.val 0
def CollF25 : Collineation5 where
  p := CollF25_p
  pinv := CollF25_pi
  l := CollF25_l
  linv := CollF25_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
