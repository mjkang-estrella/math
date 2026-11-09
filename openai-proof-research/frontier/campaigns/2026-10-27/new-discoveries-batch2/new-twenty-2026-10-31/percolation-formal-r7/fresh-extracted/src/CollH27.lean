import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH27_p (x : Points 5) : Points 5 := ([0, 7, 14, 16, 23, 5, 12, 19, 21, 3, 10, 17, 24, 1, 8, 15, 22, 4, 6, 13, 20, 2, 9, 11, 18, 25, 26, 28, 29, 30, 27] : List (Points 5)).getD x.val 0
def CollH27_pi (x : Points 5) : Points 5 := ([0, 13, 21, 9, 17, 5, 18, 1, 14, 22, 10, 23, 6, 19, 2, 15, 3, 11, 24, 7, 20, 8, 16, 4, 12, 25, 26, 30, 27, 28, 29] : List (Points 5)).getD x.val 0
def CollH27_l (x : Points 5) : Points 5 := ([0, 3, 1, 4, 2, 7, 5, 8, 6, 9, 14, 12, 10, 13, 11, 16, 19, 17, 15, 18, 23, 21, 24, 22, 20, 27, 25, 28, 26, 29, 30] : List (Points 5)).getD x.val 0
def CollH27_li (x : Points 5) : Points 5 := ([0, 2, 4, 1, 3, 6, 8, 5, 7, 9, 12, 14, 11, 13, 10, 18, 15, 17, 19, 16, 24, 21, 23, 20, 22, 26, 28, 25, 27, 29, 30] : List (Points 5)).getD x.val 0
def CollH27 : Collineation5 where
  p := CollH27_p
  pinv := CollH27_pi
  l := CollH27_l
  linv := CollH27_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
