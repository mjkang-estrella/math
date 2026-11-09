import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG04_p (x : Points 5) : Points 5 := ([0, 15, 20, 10, 25, 2, 13, 16, 28, 24, 1, 22, 29, 18, 14, 3, 27, 12, 21, 19, 30, 6, 8, 7, 9, 4, 17, 23, 11, 26, 5] : List (Points 5)).getD x.val 0
def CollG04_pi (x : Points 5) : Points 5 := ([0, 10, 5, 15, 25, 30, 21, 23, 22, 24, 3, 28, 17, 6, 14, 1, 7, 26, 13, 19, 2, 18, 11, 27, 9, 4, 29, 16, 8, 12, 20] : List (Points 5)).getD x.val 0
def CollG04_l (x : Points 5) : Points 5 := ([21, 1, 6, 11, 16, 20, 0, 5, 10, 15, 24, 4, 9, 14, 19, 23, 3, 8, 13, 18, 22, 2, 7, 12, 17, 30, 29, 27, 28, 26, 25] : List (Points 5)).getD x.val 0
def CollG04_li (x : Points 5) : Points 5 := ([6, 1, 21, 16, 11, 7, 2, 22, 17, 12, 8, 3, 23, 18, 13, 9, 4, 24, 19, 14, 5, 0, 20, 15, 10, 30, 29, 27, 28, 26, 25] : List (Points 5)).getD x.val 0
def CollG04 : Collineation5 where
  p := CollG04_p
  pinv := CollG04_pi
  l := CollG04_l
  linv := CollG04_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
