import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG21_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 13, 19, 7, 26, 20, 9, 12, 28, 15, 23, 17, 27, 10, 8, 24, 29, 5, 18, 14, 22, 21, 11, 16, 6, 25, 1] : List (Points 5)).getD x.val 0
def CollG21_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 21, 28, 7, 18, 10, 17, 26, 11, 5, 23, 13, 27, 15, 22, 6, 9, 25, 24, 14, 19, 29, 8, 16, 12, 20, 4] : List (Points 5)).getD x.val 0
def CollG21_l (x : Points 5) : Points 5 := ([4, 5, 11, 17, 23, 24, 0, 6, 12, 18, 19, 20, 1, 7, 13, 14, 15, 21, 2, 8, 9, 10, 16, 22, 3, 25, 30, 27, 29, 28, 26] : List (Points 5)).getD x.val 0
def CollG21_li (x : Points 5) : Points 5 := ([6, 12, 18, 24, 0, 1, 7, 13, 19, 20, 21, 2, 8, 14, 15, 16, 22, 3, 9, 10, 11, 17, 23, 4, 5, 25, 30, 27, 29, 28, 26] : List (Points 5)).getD x.val 0
def CollG21 : Collineation5 where
  p := CollG21_p
  pinv := CollG21_pi
  l := CollG21_l
  linv := CollG21_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
