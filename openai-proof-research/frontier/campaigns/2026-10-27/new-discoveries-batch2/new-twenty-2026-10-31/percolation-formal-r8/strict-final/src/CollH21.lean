import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH21_p (x : Points 5) : Points 5 := ([0, 13, 9, 17, 29, 5, 3, 19, 12, 27, 10, 18, 4, 7, 28, 15, 8, 14, 2, 26, 20, 23, 24, 22, 30, 25, 1, 11, 6, 16, 21] : List (Points 5)).getD x.val 0
def CollH21_pi (x : Points 5) : Points 5 := ([0, 26, 18, 6, 12, 5, 28, 13, 16, 2, 10, 27, 8, 1, 17, 15, 29, 3, 11, 7, 20, 30, 23, 21, 22, 25, 19, 9, 14, 4, 24] : List (Points 5)).getD x.val 0
def CollH21_l (x : Points 5) : Points 5 := ([4, 0, 1, 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 10, 17, 18, 19, 15, 16, 23, 24, 20, 21, 22, 26, 27, 28, 29, 25, 30] : List (Points 5)).getD x.val 0
def CollH21_li (x : Points 5) : Points 5 := ([1, 2, 3, 4, 0, 5, 6, 7, 8, 9, 14, 10, 11, 12, 13, 18, 19, 15, 16, 17, 22, 23, 24, 20, 21, 29, 25, 26, 27, 28, 30] : List (Points 5)).getD x.val 0
def CollH21 : Collineation5 where
  p := CollH21_p
  pinv := CollH21_pi
  l := CollH21_l
  linv := CollH21_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
