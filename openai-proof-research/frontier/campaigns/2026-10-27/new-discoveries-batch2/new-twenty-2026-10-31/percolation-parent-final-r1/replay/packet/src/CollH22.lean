import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH22_p (x : Points 5) : Points 5 := ([0, 11, 8, 19, 28, 5, 1, 18, 14, 29, 10, 16, 3, 9, 26, 15, 6, 13, 4, 27, 20, 21, 23, 24, 30, 25, 2, 12, 7, 17, 22] : List (Points 5)).getD x.val 0
def CollH22_pi (x : Points 5) : Points 5 := ([0, 6, 26, 12, 18, 5, 16, 28, 2, 13, 10, 1, 27, 17, 8, 15, 11, 29, 7, 3, 20, 21, 30, 22, 23, 25, 14, 19, 4, 9, 24] : List (Points 5)).getD x.val 0
def CollH22_l (x : Points 5) : Points 5 := ([2, 0, 3, 1, 4, 5, 8, 6, 9, 7, 13, 11, 14, 12, 10, 16, 19, 17, 15, 18, 24, 22, 20, 23, 21, 28, 26, 29, 27, 25, 30] : List (Points 5)).getD x.val 0
def CollH22_li (x : Points 5) : Points 5 := ([1, 3, 0, 2, 4, 5, 7, 9, 6, 8, 14, 11, 13, 10, 12, 18, 15, 17, 19, 16, 22, 24, 21, 23, 20, 29, 26, 28, 25, 27, 30] : List (Points 5)).getD x.val 0
def CollH22 : Collineation5 where
  p := CollH22_p
  pinv := CollH22_pi
  l := CollH22_l
  linv := CollH22_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
