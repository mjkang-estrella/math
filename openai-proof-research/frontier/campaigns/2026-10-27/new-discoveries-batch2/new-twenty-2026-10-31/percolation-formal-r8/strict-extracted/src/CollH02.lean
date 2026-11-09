import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH02_p (x : Points 5) : Points 5 := ([0, 1, 3, 4, 30, 5, 16, 13, 24, 28, 10, 6, 23, 19, 29, 15, 21, 8, 14, 26, 20, 11, 18, 9, 27, 25, 7, 17, 12, 22, 2] : List (Points 5)).getD x.val 0
def CollH02_pi (x : Points 5) : Points 5 := ([0, 1, 30, 2, 3, 5, 11, 26, 17, 23, 10, 21, 28, 7, 18, 15, 6, 27, 22, 13, 20, 16, 29, 12, 8, 25, 19, 24, 9, 14, 4] : List (Points 5)).getD x.val 0
def CollH02_l (x : Points 5) : Points 5 := ([2, 0, 3, 1, 4, 7, 5, 8, 6, 9, 12, 10, 13, 11, 14, 17, 15, 18, 16, 19, 22, 20, 23, 21, 24, 25, 28, 26, 29, 27, 30] : List (Points 5)).getD x.val 0
def CollH02_li (x : Points 5) : Points 5 := ([1, 3, 0, 2, 4, 6, 8, 5, 7, 9, 11, 13, 10, 12, 14, 16, 18, 15, 17, 19, 21, 23, 20, 22, 24, 25, 27, 29, 26, 28, 30] : List (Points 5)).getD x.val 0
def CollH02 : Collineation5 where
  p := CollH02_p
  pinv := CollH02_pi
  l := CollH02_l
  linv := CollH02_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
