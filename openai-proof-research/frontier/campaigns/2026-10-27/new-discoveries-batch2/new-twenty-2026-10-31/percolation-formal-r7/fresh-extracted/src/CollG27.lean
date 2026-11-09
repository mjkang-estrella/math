import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG27_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 7, 19, 13, 20, 26, 14, 5, 22, 18, 29, 16, 21, 6, 11, 25, 23, 12, 15, 9, 28, 27, 8, 17, 10, 24, 1] : List (Points 5)).getD x.val 0
def CollG27_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 11, 17, 5, 26, 23, 28, 18, 21, 7, 10, 22, 15, 27, 13, 6, 8, 16, 12, 20, 29, 19, 9, 25, 24, 14, 4] : List (Points 5)).getD x.val 0
def CollG27_l (x : Points 5) : Points 5 := ([14, 0, 16, 7, 23, 19, 5, 21, 12, 3, 24, 10, 1, 17, 8, 4, 15, 6, 22, 13, 9, 20, 11, 2, 18, 25, 29, 26, 30, 28, 27] : List (Points 5)).getD x.val 0
def CollG27_li (x : Points 5) : Points 5 := ([1, 12, 23, 9, 15, 6, 17, 3, 14, 20, 11, 22, 8, 19, 0, 16, 2, 13, 24, 5, 21, 7, 18, 4, 10, 25, 27, 30, 29, 26, 28] : List (Points 5)).getD x.val 0
def CollG27 : Collineation5 where
  p := CollG27_p
  pinv := CollG27_pi
  l := CollG27_l
  linv := CollG27_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
