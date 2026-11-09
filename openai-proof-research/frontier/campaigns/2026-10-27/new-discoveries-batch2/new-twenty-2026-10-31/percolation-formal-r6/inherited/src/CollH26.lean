import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH26_p (x : Points 5) : Points 5 := ([0, 6, 12, 18, 24, 5, 11, 17, 23, 4, 10, 16, 22, 3, 9, 15, 21, 2, 8, 14, 20, 1, 7, 13, 19, 25, 28, 29, 27, 30, 26] : List (Points 5)).getD x.val 0
def CollH26_pi (x : Points 5) : Points 5 := ([0, 21, 17, 13, 9, 5, 1, 22, 18, 14, 10, 6, 2, 23, 19, 15, 11, 7, 3, 24, 20, 16, 12, 8, 4, 25, 30, 28, 26, 27, 29] : List (Points 5)).getD x.val 0
def CollH26_l (x : Points 5) : Points 5 := ([0, 1, 2, 3, 4, 9, 5, 6, 7, 8, 13, 14, 10, 11, 12, 17, 18, 19, 15, 16, 21, 22, 23, 24, 20, 29, 25, 26, 27, 28, 30] : List (Points 5)).getD x.val 0
def CollH26_li (x : Points 5) : Points 5 := ([0, 1, 2, 3, 4, 6, 7, 8, 9, 5, 12, 13, 14, 10, 11, 18, 19, 15, 16, 17, 24, 20, 21, 22, 23, 26, 27, 28, 29, 25, 30] : List (Points 5)).getD x.val 0
def CollH26 : Collineation5 where
  p := CollH26_p
  pinv := CollH26_pi
  l := CollH26_l
  linv := CollH26_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
