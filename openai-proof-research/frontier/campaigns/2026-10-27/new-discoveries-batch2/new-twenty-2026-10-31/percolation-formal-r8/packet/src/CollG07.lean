import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG07_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 16, 11, 21, 25, 6, 23, 15, 28, 12, 9, 14, 29, 18, 22, 5, 27, 24, 10, 17, 8, 7, 19, 13, 20, 26, 1] : List (Points 5)).getD x.val 0
def CollG07_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 19, 9, 25, 24, 14, 22, 6, 13, 27, 15, 11, 5, 23, 17, 26, 28, 7, 18, 10, 21, 8, 29, 20, 12, 16, 4] : List (Points 5)).getD x.val 0
def CollG07_l (x : Points 5) : Points 5 := ([9, 20, 11, 2, 18, 14, 0, 16, 7, 23, 19, 5, 21, 12, 3, 24, 10, 1, 17, 8, 4, 15, 6, 22, 13, 25, 29, 26, 30, 28, 27] : List (Points 5)).getD x.val 0
def CollG07_li (x : Points 5) : Points 5 := ([6, 17, 3, 14, 20, 11, 22, 8, 19, 0, 16, 2, 13, 24, 5, 21, 7, 18, 4, 10, 1, 12, 23, 9, 15, 25, 27, 30, 29, 26, 28] : List (Points 5)).getD x.val 0
def CollG07 : Collineation5 where
  p := CollG07_p
  pinv := CollG07_pi
  l := CollG07_l
  linv := CollG07_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
