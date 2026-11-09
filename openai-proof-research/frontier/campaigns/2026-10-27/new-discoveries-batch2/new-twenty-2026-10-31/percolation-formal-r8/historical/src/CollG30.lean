import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG30_p (x : Points 5) : Points 5 := ([0, 15, 20, 10, 25, 1, 18, 22, 14, 29, 2, 16, 24, 13, 28, 3, 19, 21, 12, 27, 4, 17, 23, 11, 26, 30, 6, 8, 7, 9, 5] : List (Points 5)).getD x.val 0
def CollG30_pi (x : Points 5) : Points 5 := ([0, 5, 10, 15, 20, 30, 26, 28, 27, 29, 3, 23, 18, 13, 8, 1, 11, 21, 6, 16, 2, 17, 7, 22, 12, 4, 24, 19, 14, 9, 25] : List (Points 5)).getD x.val 0
def CollG30_l (x : Points 5) : Points 5 := ([20, 0, 5, 10, 15, 21, 1, 6, 11, 16, 22, 2, 7, 12, 17, 23, 3, 8, 13, 18, 24, 4, 9, 14, 19, 30, 26, 28, 27, 29, 25] : List (Points 5)).getD x.val 0
def CollG30_li (x : Points 5) : Points 5 := ([1, 6, 11, 16, 21, 2, 7, 12, 17, 22, 3, 8, 13, 18, 23, 4, 9, 14, 19, 24, 0, 5, 10, 15, 20, 30, 26, 28, 27, 29, 25] : List (Points 5)).getD x.val 0
def CollG30 : Collineation5 where
  p := CollG30_p
  pinv := CollG30_pi
  l := CollG30_l
  linv := CollG30_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
