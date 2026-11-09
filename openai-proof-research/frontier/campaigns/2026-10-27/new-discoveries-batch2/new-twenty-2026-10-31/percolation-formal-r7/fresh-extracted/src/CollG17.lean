import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG17_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 21, 6, 11, 25, 16, 13, 20, 26, 7, 19, 9, 28, 23, 12, 15, 29, 14, 5, 22, 18, 17, 24, 8, 10, 27, 1] : List (Points 5)).getD x.val 0
def CollG17_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 22, 6, 13, 27, 15, 28, 7, 18, 10, 21, 19, 9, 25, 24, 14, 11, 5, 23, 17, 26, 8, 12, 29, 16, 20, 4] : List (Points 5)).getD x.val 0
def CollG17_l (x : Points 5) : Points 5 := ([14, 15, 21, 2, 8, 24, 0, 6, 12, 18, 9, 10, 16, 22, 3, 19, 20, 1, 7, 13, 4, 5, 11, 17, 23, 25, 27, 28, 30, 29, 26] : List (Points 5)).getD x.val 0
def CollG17_li (x : Points 5) : Points 5 := ([6, 17, 3, 14, 20, 21, 7, 18, 4, 10, 11, 22, 8, 19, 0, 1, 12, 23, 9, 15, 16, 2, 13, 24, 5, 25, 30, 26, 27, 29, 28] : List (Points 5)).getD x.val 0
def CollG17 : Collineation5 where
  p := CollG17_p
  pinv := CollG17_pi
  l := CollG17_l
  linv := CollG17_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
