import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH01_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 5, 18, 14, 22, 29, 10, 8, 24, 17, 27, 15, 23, 9, 12, 28, 20, 13, 19, 7, 26, 25, 6, 16, 11, 21, 1] : List (Points 5)).getD x.val 0
def CollH01_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 5, 26, 23, 11, 17, 10, 28, 18, 21, 7, 15, 27, 13, 6, 22, 20, 29, 8, 16, 12, 25, 24, 14, 19, 9, 4] : List (Points 5)).getD x.val 0
def CollH01_l (x : Points 5) : Points 5 := ([4, 0, 1, 2, 3, 9, 5, 6, 7, 8, 14, 10, 11, 12, 13, 19, 15, 16, 17, 18, 24, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30] : List (Points 5)).getD x.val 0
def CollH01_li (x : Points 5) : Points 5 := ([1, 2, 3, 4, 0, 6, 7, 8, 9, 5, 11, 12, 13, 14, 10, 16, 17, 18, 19, 15, 21, 22, 23, 24, 20, 25, 26, 27, 28, 29, 30] : List (Points 5)).getD x.val 0
def CollH01 : Collineation5 where
  p := CollH01_p
  pinv := CollH01_pi
  l := CollH01_l
  linv := CollH01_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
