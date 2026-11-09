import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH17_p (x : Points 5) : Points 5 := ([0, 21, 13, 9, 29, 5, 11, 23, 4, 26, 10, 1, 8, 24, 27, 15, 16, 18, 19, 30, 20, 6, 3, 14, 28, 25, 22, 7, 2, 12, 17] : List (Points 5)).getD x.val 0
def CollH17_pi (x : Points 5) : Points 5 := ([0, 11, 28, 22, 8, 5, 21, 27, 12, 3, 10, 6, 29, 2, 23, 15, 16, 30, 17, 18, 20, 1, 26, 7, 13, 25, 9, 14, 24, 4, 19] : List (Points 5)).getD x.val 0
def CollH17_l (x : Points 5) : Points 5 := ([2, 0, 3, 1, 4, 8, 6, 9, 7, 5, 14, 12, 10, 13, 11, 15, 18, 16, 19, 17, 21, 24, 22, 20, 23, 26, 29, 27, 25, 28, 30] : List (Points 5)).getD x.val 0
def CollH17_li (x : Points 5) : Points 5 := ([1, 3, 0, 2, 4, 9, 6, 8, 5, 7, 12, 14, 11, 13, 10, 15, 17, 19, 16, 18, 23, 20, 22, 24, 21, 28, 25, 27, 29, 26, 30] : List (Points 5)).getD x.val 0
def CollH17 : Collineation5 where
  p := CollH17_p
  pinv := CollH17_pi
  l := CollH17_l
  linv := CollH17_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
