import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH30_p (x : Points 5) : Points 5 := ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30] : List (Points 5)).getD x.val 0
def CollH30_pi (x : Points 5) : Points 5 := ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30] : List (Points 5)).getD x.val 0
def CollH30_l (x : Points 5) : Points 5 := ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30] : List (Points 5)).getD x.val 0
def CollH30_li (x : Points 5) : Points 5 := ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30] : List (Points 5)).getD x.val 0
def CollH30 : Collineation5 where
  p := CollH30_p
  pinv := CollH30_pi
  l := CollH30_l
  linv := CollH30_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
