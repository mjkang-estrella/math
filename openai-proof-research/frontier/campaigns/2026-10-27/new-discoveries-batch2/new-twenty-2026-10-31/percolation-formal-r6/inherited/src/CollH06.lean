import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH06_p (x : Points 5) : Points 5 := ([0, 18, 24, 12, 26, 5, 8, 9, 7, 30, 10, 23, 19, 2, 29, 15, 13, 4, 22, 27, 20, 3, 14, 17, 28, 25, 11, 21, 16, 1, 6] : List (Points 5)).getD x.val 0
def CollH06_pi (x : Points 5) : Points 5 := ([0, 29, 13, 21, 17, 5, 30, 8, 6, 7, 10, 26, 3, 16, 22, 15, 28, 23, 1, 12, 20, 27, 18, 11, 2, 25, 4, 19, 24, 14, 9] : List (Points 5)).getD x.val 0
def CollH06_l (x : Points 5) : Points 5 := ([4, 0, 1, 2, 3, 8, 9, 5, 6, 7, 12, 13, 14, 10, 11, 16, 17, 18, 19, 15, 20, 21, 22, 23, 24, 29, 25, 26, 27, 28, 30] : List (Points 5)).getD x.val 0
def CollH06_li (x : Points 5) : Points 5 := ([1, 2, 3, 4, 0, 7, 8, 9, 5, 6, 13, 14, 10, 11, 12, 19, 15, 16, 17, 18, 20, 21, 22, 23, 24, 26, 27, 28, 29, 25, 30] : List (Points 5)).getD x.val 0
def CollH06 : Collineation5 where
  p := CollH06_p
  pinv := CollH06_pi
  l := CollH06_l
  linv := CollH06_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
