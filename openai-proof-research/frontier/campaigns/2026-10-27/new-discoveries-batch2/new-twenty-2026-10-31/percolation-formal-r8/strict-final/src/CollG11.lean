import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG11_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 8, 24, 17, 27, 10, 19, 7, 26, 20, 13, 22, 29, 5, 18, 14, 28, 15, 23, 9, 12, 11, 6, 21, 16, 25, 1] : List (Points 5)).getD x.val 0
def CollG11_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 17, 26, 11, 5, 23, 9, 25, 24, 14, 19, 21, 28, 7, 18, 10, 13, 27, 15, 22, 6, 29, 12, 8, 20, 16, 4] : List (Points 5)).getD x.val 0
def CollG11_l (x : Points 5) : Points 5 := ([4, 10, 21, 7, 18, 19, 0, 11, 22, 8, 9, 15, 1, 12, 23, 24, 5, 16, 2, 13, 14, 20, 6, 17, 3, 25, 30, 26, 27, 29, 28] : List (Points 5)).getD x.val 0
def CollG11_li (x : Points 5) : Points 5 := ([6, 12, 18, 24, 0, 16, 22, 3, 9, 10, 1, 7, 13, 19, 20, 11, 17, 23, 4, 5, 21, 2, 8, 14, 15, 25, 27, 28, 30, 29, 26] : List (Points 5)).getD x.val 0
def CollG11 : Collineation5 where
  p := CollG11_p
  pinv := CollG11_pi
  l := CollG11_l
  linv := CollG11_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
