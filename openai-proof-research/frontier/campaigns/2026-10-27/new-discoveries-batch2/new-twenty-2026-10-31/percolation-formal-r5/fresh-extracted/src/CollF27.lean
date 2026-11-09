import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF27_p (x : Points 5) : Points 5 := ([27, 8, 17, 10, 24, 7, 19, 13, 20, 26, 16, 11, 21, 25, 6, 14, 22, 29, 5, 18, 23, 28, 9, 15, 12, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF27_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 18, 14, 5, 1, 22, 3, 11, 24, 7, 15, 23, 10, 2, 19, 6, 8, 12, 16, 20, 4, 13, 9, 0, 21, 17, 29] : List (Points 5)).getD x.val 0
def CollF27_l (x : Points 5) : Points 5 := ([25, 29, 26, 30, 28, 19, 5, 21, 12, 3, 4, 22, 15, 13, 6, 24, 1, 8, 10, 17, 9, 18, 2, 11, 20, 14, 0, 16, 7, 23, 27] : List (Points 5)).getD x.val 0
def CollF27_li (x : Points 5) : Points 5 := ([26, 16, 22, 9, 10, 6, 14, 28, 17, 20, 18, 23, 8, 13, 25, 12, 27, 19, 21, 5, 24, 7, 11, 29, 15, 0, 2, 30, 4, 1, 3] : List (Points 5)).getD x.val 0
def CollF27 : Collineation5 where
  p := CollF27_p
  pinv := CollF27_pi
  l := CollF27_l
  linv := CollF27_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
