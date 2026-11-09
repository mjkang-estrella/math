import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG05_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 15, 12, 23, 28, 9, 20, 19, 26, 13, 7, 10, 27, 17, 24, 8, 25, 21, 11, 16, 6, 5, 18, 14, 22, 29, 1] : List (Points 5)).getD x.val 0
def CollG05_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 25, 24, 14, 19, 9, 15, 22, 6, 13, 27, 5, 23, 17, 26, 11, 10, 21, 28, 7, 18, 20, 12, 16, 8, 29, 4] : List (Points 5)).getD x.val 0
def CollG05_l (x : Points 5) : Points 5 := ([24, 20, 21, 22, 23, 4, 0, 1, 2, 3, 9, 5, 6, 7, 8, 14, 10, 11, 12, 13, 19, 15, 16, 17, 18, 25, 26, 27, 28, 29, 30] : List (Points 5)).getD x.val 0
def CollG05_li (x : Points 5) : Points 5 := ([6, 7, 8, 9, 5, 11, 12, 13, 14, 10, 16, 17, 18, 19, 15, 21, 22, 23, 24, 20, 1, 2, 3, 4, 0, 25, 26, 27, 28, 29, 30] : List (Points 5)).getD x.val 0
def CollG05 : Collineation5 where
  p := CollG05_p
  pinv := CollG05_pi
  l := CollG05_l
  linv := CollG05_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
