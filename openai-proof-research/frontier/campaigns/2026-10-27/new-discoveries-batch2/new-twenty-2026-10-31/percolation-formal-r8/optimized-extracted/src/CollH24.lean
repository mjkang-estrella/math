import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH24_p (x : Points 5) : Points 5 := ([0, 12, 6, 18, 26, 5, 2, 16, 13, 28, 10, 17, 1, 8, 27, 15, 7, 11, 3, 29, 20, 22, 21, 23, 30, 25, 4, 14, 9, 19, 24] : List (Points 5)).getD x.val 0
def CollH24_pi (x : Points 5) : Points 5 := ([0, 12, 6, 18, 26, 5, 2, 16, 13, 28, 10, 17, 1, 8, 27, 15, 7, 11, 3, 29, 20, 22, 21, 23, 30, 25, 4, 14, 9, 19, 24] : List (Points 5)).getD x.val 0
def CollH24_l (x : Points 5) : Points 5 := ([1, 0, 4, 3, 2, 5, 9, 8, 7, 6, 14, 13, 12, 11, 10, 18, 17, 16, 15, 19, 22, 21, 20, 24, 23, 29, 28, 27, 26, 25, 30] : List (Points 5)).getD x.val 0
def CollH24_li (x : Points 5) : Points 5 := ([1, 0, 4, 3, 2, 5, 9, 8, 7, 6, 14, 13, 12, 11, 10, 18, 17, 16, 15, 19, 22, 21, 20, 24, 23, 29, 28, 27, 26, 25, 30] : List (Points 5)).getD x.val 0
def CollH24 : Collineation5 where
  p := CollH24_p
  pinv := CollH24_pi
  l := CollH24_l
  linv := CollH24_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
