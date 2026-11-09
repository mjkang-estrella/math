import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG02_p (x : Points 5) : Points 5 := ([0, 15, 20, 10, 25, 1, 14, 18, 29, 22, 3, 21, 27, 19, 12, 4, 26, 11, 23, 17, 30, 8, 9, 6, 7, 2, 16, 24, 13, 28, 5] : List (Points 5)).getD x.val 0
def CollG02_pi (x : Points 5) : Points 5 := ([0, 5, 25, 10, 15, 30, 23, 24, 21, 22, 3, 17, 14, 28, 6, 1, 26, 19, 7, 13, 2, 11, 9, 18, 27, 4, 16, 12, 29, 8, 20] : List (Points 5)).getD x.val 0
def CollG02_l (x : Points 5) : Points 5 := ([22, 2, 7, 12, 17, 20, 0, 5, 10, 15, 23, 3, 8, 13, 18, 21, 1, 6, 11, 16, 24, 4, 9, 14, 19, 30, 28, 29, 26, 27, 25] : List (Points 5)).getD x.val 0
def CollG02_li (x : Points 5) : Points 5 := ([6, 16, 1, 11, 21, 7, 17, 2, 12, 22, 8, 18, 3, 13, 23, 9, 19, 4, 14, 24, 5, 15, 0, 10, 20, 30, 28, 29, 26, 27, 25] : List (Points 5)).getD x.val 0
def CollG02 : Collineation5 where
  p := CollG02_p
  pinv := CollG02_pi
  l := CollG02_l
  linv := CollG02_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
