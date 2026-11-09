import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH14_p (x : Points 5) : Points 5 := ([0, 7, 16, 23, 27, 5, 22, 1, 18, 29, 10, 12, 11, 13, 30, 15, 2, 21, 8, 26, 20, 17, 6, 3, 28, 25, 19, 4, 24, 9, 14] : List (Points 5)).getD x.val 0
def CollH14_pi (x : Points 5) : Points 5 := ([0, 7, 16, 23, 27, 5, 22, 1, 18, 29, 10, 12, 11, 13, 30, 15, 2, 21, 8, 26, 20, 17, 6, 3, 28, 25, 19, 4, 24, 9, 14] : List (Points 5)).getD x.val 0
def CollH14_l (x : Points 5) : Points 5 := ([1, 0, 4, 3, 2, 8, 7, 6, 5, 9, 10, 14, 13, 12, 11, 17, 16, 15, 19, 18, 24, 23, 22, 21, 20, 27, 26, 25, 29, 28, 30] : List (Points 5)).getD x.val 0
def CollH14_li (x : Points 5) : Points 5 := ([1, 0, 4, 3, 2, 8, 7, 6, 5, 9, 10, 14, 13, 12, 11, 17, 16, 15, 19, 18, 24, 23, 22, 21, 20, 27, 26, 25, 29, 28, 30] : List (Points 5)).getD x.val 0
def CollH14 : Collineation5 where
  p := CollH14_p
  pinv := CollH14_pi
  l := CollH14_l
  linv := CollH14_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
