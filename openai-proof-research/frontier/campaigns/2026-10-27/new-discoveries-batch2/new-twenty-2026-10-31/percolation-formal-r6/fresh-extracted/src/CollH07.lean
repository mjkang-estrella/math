import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH07_p (x : Points 5) : Points 5 := ([0, 16, 23, 14, 27, 5, 6, 8, 9, 30, 10, 21, 18, 4, 28, 15, 11, 3, 24, 29, 20, 1, 13, 19, 26, 25, 12, 22, 17, 2, 7] : List (Points 5)).getD x.val 0
def CollH07_pi (x : Points 5) : Points 5 := ([0, 21, 29, 17, 13, 5, 6, 30, 7, 8, 10, 16, 26, 22, 3, 15, 1, 28, 12, 23, 20, 11, 27, 2, 18, 25, 24, 4, 14, 19, 9] : List (Points 5)).getD x.val 0
def CollH07_l (x : Points 5) : Points 5 := ([2, 0, 3, 1, 4, 9, 7, 5, 8, 6, 11, 14, 12, 10, 13, 18, 16, 19, 17, 15, 20, 23, 21, 24, 22, 27, 25, 28, 26, 29, 30] : List (Points 5)).getD x.val 0
def CollH07_li (x : Points 5) : Points 5 := ([1, 3, 0, 2, 4, 7, 9, 6, 8, 5, 13, 10, 12, 14, 11, 19, 16, 18, 15, 17, 20, 22, 24, 21, 23, 26, 28, 25, 27, 29, 30] : List (Points 5)).getD x.val 0
def CollH07 : Collineation5 where
  p := CollH07_p
  pinv := CollH07_pi
  l := CollH07_l
  linv := CollH07_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
