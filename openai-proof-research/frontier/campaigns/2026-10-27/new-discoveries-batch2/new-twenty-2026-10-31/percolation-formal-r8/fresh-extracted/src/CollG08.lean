import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG08_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 19, 13, 20, 26, 7, 22, 18, 29, 14, 5, 11, 25, 16, 21, 6, 28, 23, 12, 15, 9, 8, 17, 10, 24, 27, 1] : List (Points 5)).getD x.val 0
def CollG08_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 14, 19, 9, 25, 24, 27, 15, 22, 6, 13, 23, 17, 26, 11, 5, 7, 18, 10, 21, 28, 16, 8, 29, 20, 12, 4] : List (Points 5)).getD x.val 0
def CollG08_l (x : Points 5) : Points 5 := ([14, 20, 6, 17, 3, 19, 0, 11, 22, 8, 24, 5, 16, 2, 13, 4, 10, 21, 7, 18, 9, 15, 1, 12, 23, 25, 27, 30, 29, 26, 28] : List (Points 5)).getD x.val 0
def CollG08_li (x : Points 5) : Points 5 := ([6, 22, 13, 4, 15, 11, 2, 18, 9, 20, 16, 7, 23, 14, 0, 21, 12, 3, 19, 5, 1, 17, 8, 24, 10, 25, 29, 26, 30, 28, 27] : List (Points 5)).getD x.val 0
def CollG08 : Collineation5 where
  p := CollG08_p
  pinv := CollG08_pi
  l := CollG08_l
  linv := CollG08_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
