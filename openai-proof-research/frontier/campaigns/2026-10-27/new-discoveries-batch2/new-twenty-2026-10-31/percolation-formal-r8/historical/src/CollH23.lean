import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH23_p (x : Points 5) : Points 5 := ([0, 14, 7, 16, 27, 5, 4, 17, 11, 26, 10, 19, 2, 6, 29, 15, 9, 12, 1, 28, 20, 24, 22, 21, 30, 25, 3, 13, 8, 18, 23] : List (Points 5)).getD x.val 0
def CollH23_pi (x : Points 5) : Points 5 := ([0, 18, 12, 26, 6, 5, 13, 2, 28, 16, 10, 8, 17, 27, 1, 15, 3, 7, 29, 11, 20, 23, 22, 30, 21, 25, 9, 4, 19, 14, 24] : List (Points 5)).getD x.val 0
def CollH23_l (x : Points 5) : Points 5 := ([3, 0, 2, 4, 1, 5, 7, 9, 6, 8, 12, 14, 11, 13, 10, 19, 16, 18, 15, 17, 21, 23, 20, 22, 24, 27, 29, 26, 28, 25, 30] : List (Points 5)).getD x.val 0
def CollH23_li (x : Points 5) : Points 5 := ([1, 4, 2, 0, 3, 5, 8, 6, 9, 7, 14, 12, 10, 13, 11, 18, 16, 19, 17, 15, 22, 20, 23, 21, 24, 29, 27, 25, 28, 26, 30] : List (Points 5)).getD x.val 0
def CollH23 : Collineation5 where
  p := CollH23_p
  pinv := CollH23_pi
  l := CollH23_l
  linv := CollH23_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
