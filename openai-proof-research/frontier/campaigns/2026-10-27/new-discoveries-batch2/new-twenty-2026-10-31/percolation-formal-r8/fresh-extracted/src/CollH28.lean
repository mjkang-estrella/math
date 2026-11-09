import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH28_p (x : Points 5) : Points 5 := ([0, 8, 11, 19, 22, 5, 13, 16, 24, 2, 10, 18, 21, 4, 7, 15, 23, 1, 9, 12, 20, 3, 6, 14, 17, 25, 29, 27, 26, 30, 28] : List (Points 5)).getD x.val 0
def CollH28_pi (x : Points 5) : Points 5 := ([0, 17, 9, 21, 13, 5, 22, 14, 1, 18, 10, 2, 19, 6, 23, 15, 7, 24, 11, 3, 20, 12, 4, 16, 8, 25, 28, 27, 30, 26, 29] : List (Points 5)).getD x.val 0
def CollH28_l (x : Points 5) : Points 5 := ([0, 2, 4, 1, 3, 8, 5, 7, 9, 6, 11, 13, 10, 12, 14, 19, 16, 18, 15, 17, 22, 24, 21, 23, 20, 28, 25, 27, 29, 26, 30] : List (Points 5)).getD x.val 0
def CollH28_li (x : Points 5) : Points 5 := ([0, 3, 1, 4, 2, 6, 9, 7, 5, 8, 12, 10, 13, 11, 14, 18, 16, 19, 17, 15, 24, 22, 20, 23, 21, 26, 29, 27, 25, 28, 30] : List (Points 5)).getD x.val 0
def CollH28 : Collineation5 where
  p := CollH28_p
  pinv := CollH28_pi
  l := CollH28_l
  linv := CollH28_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
