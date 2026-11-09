import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH04_p (x : Points 5) : Points 5 := ([0, 2, 1, 3, 30, 5, 17, 11, 23, 26, 10, 7, 21, 18, 28, 15, 22, 6, 13, 27, 20, 12, 16, 8, 29, 25, 9, 19, 14, 24, 4] : List (Points 5)).getD x.val 0
def CollH04_pi (x : Points 5) : Points 5 := ([0, 2, 1, 3, 30, 5, 17, 11, 23, 26, 10, 7, 21, 18, 28, 15, 22, 6, 13, 27, 20, 12, 16, 8, 29, 25, 9, 19, 14, 24, 4] : List (Points 5)).getD x.val 0
def CollH04_l (x : Points 5) : Points 5 := ([1, 0, 4, 3, 2, 6, 5, 9, 8, 7, 11, 10, 14, 13, 12, 16, 15, 19, 18, 17, 21, 20, 24, 23, 22, 25, 29, 28, 27, 26, 30] : List (Points 5)).getD x.val 0
def CollH04_li (x : Points 5) : Points 5 := ([1, 0, 4, 3, 2, 6, 5, 9, 8, 7, 11, 10, 14, 13, 12, 16, 15, 19, 18, 17, 21, 20, 24, 23, 22, 25, 29, 28, 27, 26, 30] : List (Points 5)).getD x.val 0
def CollH04 : Collineation5 where
  p := CollH04_p
  pinv := CollH04_pi
  l := CollH04_l
  linv := CollH04_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
