import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG28_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 8, 17, 10, 24, 27, 11, 6, 21, 16, 25, 19, 20, 7, 13, 26, 22, 14, 18, 5, 29, 28, 9, 15, 12, 23, 1] : List (Points 5)).getD x.val 0
def CollG28_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 23, 11, 17, 5, 26, 7, 10, 28, 18, 21, 27, 13, 6, 22, 15, 16, 12, 20, 29, 8, 14, 19, 9, 25, 24, 4] : List (Points 5)).getD x.val 0
def CollG28_l (x : Points 5) : Points 5 := ([19, 0, 11, 22, 8, 24, 5, 16, 2, 13, 4, 10, 21, 7, 18, 9, 15, 1, 12, 23, 14, 20, 6, 17, 3, 25, 27, 30, 29, 26, 28] : List (Points 5)).getD x.val 0
def CollG28_li (x : Points 5) : Points 5 := ([1, 17, 8, 24, 10, 6, 22, 13, 4, 15, 11, 2, 18, 9, 20, 16, 7, 23, 14, 0, 21, 12, 3, 19, 5, 25, 29, 26, 30, 28, 27] : List (Points 5)).getD x.val 0
def CollG28 : Collineation5 where
  p := CollG28_p
  pinv := CollG28_pi
  l := CollG28_l
  linv := CollG28_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
