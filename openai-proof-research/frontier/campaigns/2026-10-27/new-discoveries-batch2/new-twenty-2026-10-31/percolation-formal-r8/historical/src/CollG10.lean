import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG10_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 5, 22, 18, 29, 14, 15, 9, 28, 23, 12, 20, 26, 7, 19, 13, 25, 16, 21, 6, 11, 10, 8, 24, 17, 27, 1] : List (Points 5)).getD x.val 0
def CollG10_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 5, 23, 17, 26, 11, 25, 24, 14, 19, 9, 10, 21, 28, 7, 18, 15, 22, 6, 13, 27, 20, 16, 29, 12, 8, 4] : List (Points 5)).getD x.val 0
def CollG10_l (x : Points 5) : Points 5 := ([14, 10, 11, 12, 13, 4, 0, 1, 2, 3, 19, 15, 16, 17, 18, 9, 5, 6, 7, 8, 24, 20, 21, 22, 23, 25, 27, 29, 26, 28, 30] : List (Points 5)).getD x.val 0
def CollG10_li (x : Points 5) : Points 5 := ([6, 7, 8, 9, 5, 16, 17, 18, 19, 15, 1, 2, 3, 4, 0, 11, 12, 13, 14, 10, 21, 22, 23, 24, 20, 25, 28, 26, 29, 27, 30] : List (Points 5)).getD x.val 0
def CollG10 : Collineation5 where
  p := CollG10_p
  pinv := CollG10_pi
  l := CollG10_l
  linv := CollG10_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
