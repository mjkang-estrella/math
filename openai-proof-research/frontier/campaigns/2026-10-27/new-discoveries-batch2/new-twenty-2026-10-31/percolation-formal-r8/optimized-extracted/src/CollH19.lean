import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH19_p (x : Points 5) : Points 5 := ([0, 22, 11, 8, 28, 5, 12, 21, 3, 27, 10, 2, 6, 23, 29, 15, 17, 16, 18, 30, 20, 7, 1, 13, 26, 25, 24, 9, 4, 14, 19] : List (Points 5)).getD x.val 0
def CollH19_pi (x : Points 5) : Points 5 := ([0, 22, 11, 8, 28, 5, 12, 21, 3, 27, 10, 2, 6, 23, 29, 15, 17, 16, 18, 30, 20, 7, 1, 13, 26, 25, 24, 9, 4, 14, 19] : List (Points 5)).getD x.val 0
def CollH19_l (x : Points 5) : Points 5 := ([1, 0, 4, 3, 2, 9, 8, 7, 6, 5, 12, 11, 10, 14, 13, 15, 19, 18, 17, 16, 23, 22, 21, 20, 24, 28, 27, 26, 25, 29, 30] : List (Points 5)).getD x.val 0
def CollH19_li (x : Points 5) : Points 5 := ([1, 0, 4, 3, 2, 9, 8, 7, 6, 5, 12, 11, 10, 14, 13, 15, 19, 18, 17, 16, 23, 22, 21, 20, 24, 28, 27, 26, 25, 29, 30] : List (Points 5)).getD x.val 0
def CollH19 : Collineation5 where
  p := CollH19_p
  pinv := CollH19_pi
  l := CollH19_l
  linv := CollH19_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
