import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH08_p (x : Points 5) : Points 5 := ([0, 19, 22, 11, 28, 5, 9, 7, 6, 30, 10, 24, 17, 1, 27, 15, 14, 2, 21, 26, 20, 4, 12, 16, 29, 25, 13, 23, 18, 3, 8] : List (Points 5)).getD x.val 0
def CollH08_pi (x : Points 5) : Points 5 := ([0, 13, 17, 29, 21, 5, 8, 7, 30, 6, 10, 3, 22, 26, 16, 15, 23, 12, 28, 1, 20, 18, 2, 27, 11, 25, 19, 14, 4, 24, 9] : List (Points 5)).getD x.val 0
def CollH08_l (x : Points 5) : Points 5 := ([3, 0, 2, 4, 1, 6, 8, 5, 7, 9, 14, 11, 13, 10, 12, 17, 19, 16, 18, 15, 20, 22, 24, 21, 23, 28, 25, 27, 29, 26, 30] : List (Points 5)).getD x.val 0
def CollH08_li (x : Points 5) : Points 5 := ([1, 4, 2, 0, 3, 7, 5, 8, 6, 9, 13, 11, 14, 12, 10, 19, 17, 15, 18, 16, 20, 23, 21, 24, 22, 26, 29, 27, 25, 28, 30] : List (Points 5)).getD x.val 0
def CollH08 : Collineation5 where
  p := CollH08_p
  pinv := CollH08_pi
  l := CollH08_l
  linv := CollH08_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
