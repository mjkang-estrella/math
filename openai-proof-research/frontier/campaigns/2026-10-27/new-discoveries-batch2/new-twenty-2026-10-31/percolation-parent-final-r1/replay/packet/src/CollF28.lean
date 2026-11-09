import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF28_p (x : Points 5) : Points 5 := ([28, 9, 15, 12, 23, 8, 17, 10, 24, 27, 19, 13, 20, 26, 7, 11, 21, 25, 6, 16, 22, 29, 5, 18, 14, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF28_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 22, 18, 14, 5, 1, 7, 15, 3, 11, 24, 2, 19, 6, 23, 10, 12, 16, 20, 4, 8, 17, 13, 9, 0, 21, 29] : List (Points 5)).getD x.val 0
def CollF28_l (x : Points 5) : Points 5 := ([25, 27, 30, 29, 26, 24, 5, 16, 2, 13, 9, 12, 15, 23, 1, 4, 21, 18, 10, 7, 14, 3, 17, 6, 20, 19, 0, 11, 22, 8, 28] : List (Points 5)).getD x.val 0
def CollF28_li (x : Points 5) : Points 5 := ([26, 14, 8, 21, 15, 6, 23, 19, 29, 10, 18, 27, 11, 9, 20, 12, 7, 22, 17, 25, 24, 16, 28, 13, 5, 0, 4, 1, 30, 3, 2] : List (Points 5)).getD x.val 0
def CollF28 : Collineation5 where
  p := CollF28_p
  pinv := CollF28_pi
  l := CollF28_l
  linv := CollF28_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
