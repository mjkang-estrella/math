import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH12_p (x : Points 5) : Points 5 := ([0, 6, 18, 24, 26, 5, 21, 3, 19, 27, 10, 11, 13, 14, 30, 15, 1, 23, 9, 28, 20, 16, 8, 4, 29, 25, 17, 2, 22, 7, 12] : List (Points 5)).getD x.val 0
def CollH12_pi (x : Points 5) : Points 5 := ([0, 16, 27, 7, 23, 5, 1, 29, 22, 18, 10, 11, 30, 12, 13, 15, 21, 26, 2, 8, 20, 6, 28, 17, 3, 25, 4, 9, 19, 24, 14] : List (Points 5)).getD x.val 0
def CollH12_l (x : Points 5) : Points 5 := ([2, 0, 3, 1, 4, 6, 9, 7, 5, 8, 10, 13, 11, 14, 12, 19, 17, 15, 18, 16, 23, 21, 24, 22, 20, 29, 27, 25, 28, 26, 30] : List (Points 5)).getD x.val 0
def CollH12_li (x : Points 5) : Points 5 := ([1, 3, 0, 2, 4, 8, 5, 7, 9, 6, 10, 12, 14, 11, 13, 17, 19, 16, 18, 15, 24, 21, 23, 20, 22, 27, 29, 26, 28, 25, 30] : List (Points 5)).getD x.val 0
def CollH12 : Collineation5 where
  p := CollH12_p
  pinv := CollH12_pi
  l := CollH12_l
  linv := CollH12_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
