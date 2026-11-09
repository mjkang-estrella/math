import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG16_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 23, 9, 12, 28, 15, 14, 22, 29, 5, 18, 7, 26, 20, 13, 19, 27, 10, 8, 24, 17, 16, 21, 6, 11, 25, 1] : List (Points 5)).getD x.val 0
def CollG16_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 13, 27, 15, 22, 6, 21, 28, 7, 18, 10, 9, 25, 24, 14, 19, 17, 26, 11, 5, 23, 29, 16, 20, 8, 12, 4] : List (Points 5)).getD x.val 0
def CollG16_l (x : Points 5) : Points 5 := ([4, 15, 6, 22, 13, 14, 0, 16, 7, 23, 24, 10, 1, 17, 8, 9, 20, 11, 2, 18, 19, 5, 21, 12, 3, 25, 30, 29, 28, 26, 27] : List (Points 5)).getD x.val 0
def CollG16_li (x : Points 5) : Points 5 := ([6, 12, 18, 24, 0, 21, 2, 8, 14, 15, 11, 17, 23, 4, 5, 1, 7, 13, 19, 20, 16, 22, 3, 9, 10, 25, 29, 30, 28, 27, 26] : List (Points 5)).getD x.val 0
def CollG16 : Collineation5 where
  p := CollG16_p
  pinv := CollG16_pi
  l := CollG16_l
  linv := CollG16_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
