import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG26_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 6, 16, 11, 21, 25, 12, 9, 23, 15, 28, 18, 22, 5, 14, 29, 24, 10, 17, 8, 27, 26, 7, 19, 13, 20, 1] : List (Points 5)).getD x.val 0
def CollG26_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 17, 5, 26, 23, 11, 21, 7, 10, 28, 18, 13, 6, 22, 15, 27, 29, 8, 16, 12, 20, 9, 25, 24, 14, 19, 4] : List (Points 5)).getD x.val 0
def CollG26_l (x : Points 5) : Points 5 := ([9, 0, 21, 17, 13, 14, 5, 1, 22, 18, 19, 10, 6, 2, 23, 24, 15, 11, 7, 3, 4, 20, 16, 12, 8, 25, 30, 28, 26, 27, 29] : List (Points 5)).getD x.val 0
def CollG26_li (x : Points 5) : Points 5 := ([1, 7, 13, 19, 20, 6, 12, 18, 24, 0, 11, 17, 23, 4, 5, 16, 22, 3, 9, 10, 21, 2, 8, 14, 15, 25, 28, 29, 27, 30, 26] : List (Points 5)).getD x.val 0
def CollG26 : Collineation5 where
  p := CollG26_p
  pinv := CollG26_pi
  l := CollG26_l
  linv := CollG26_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
