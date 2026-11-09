import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH29_p (x : Points 5) : Points 5 := ([0, 9, 13, 17, 21, 5, 14, 18, 22, 1, 10, 19, 23, 2, 6, 15, 24, 3, 7, 11, 20, 4, 8, 12, 16, 25, 27, 26, 28, 30, 29] : List (Points 5)).getD x.val 0
def CollH29_pi (x : Points 5) : Points 5 := ([0, 9, 13, 17, 21, 5, 14, 18, 22, 1, 10, 19, 23, 2, 6, 15, 24, 3, 7, 11, 20, 4, 8, 12, 16, 25, 27, 26, 28, 30, 29] : List (Points 5)).getD x.val 0
def CollH29_l (x : Points 5) : Points 5 := ([0, 4, 3, 2, 1, 6, 5, 9, 8, 7, 12, 11, 10, 14, 13, 18, 17, 16, 15, 19, 24, 23, 22, 21, 20, 26, 25, 29, 28, 27, 30] : List (Points 5)).getD x.val 0
def CollH29_li (x : Points 5) : Points 5 := ([0, 4, 3, 2, 1, 6, 5, 9, 8, 7, 12, 11, 10, 14, 13, 18, 17, 16, 15, 19, 24, 23, 22, 21, 20, 26, 25, 29, 28, 27, 30] : List (Points 5)).getD x.val 0
def CollH29 : Collineation5 where
  p := CollH29_p
  pinv := CollH29_pi
  l := CollH29_l
  linv := CollH29_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
