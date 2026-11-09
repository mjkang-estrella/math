import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollH18_p (x : Points 5) : Points 5 := ([0, 24, 12, 6, 26, 5, 14, 22, 1, 29, 10, 4, 7, 21, 28, 15, 19, 17, 16, 30, 20, 9, 2, 11, 27, 25, 23, 8, 3, 13, 18] : List (Points 5)).getD x.val 0
def CollH18_pi (x : Points 5) : Points 5 := ([0, 8, 22, 28, 11, 5, 3, 12, 27, 21, 10, 23, 2, 29, 6, 15, 18, 17, 30, 16, 20, 13, 7, 26, 1, 25, 4, 24, 14, 9, 19] : List (Points 5)).getD x.val 0
def CollH18_l (x : Points 5) : Points 5 := ([3, 0, 2, 4, 1, 7, 9, 6, 8, 5, 11, 13, 10, 12, 14, 15, 17, 19, 16, 18, 24, 21, 23, 20, 22, 29, 26, 28, 25, 27, 30] : List (Points 5)).getD x.val 0
def CollH18_li (x : Points 5) : Points 5 := ([1, 4, 2, 0, 3, 9, 7, 5, 8, 6, 12, 10, 13, 11, 14, 15, 18, 16, 19, 17, 23, 21, 24, 22, 20, 28, 26, 29, 27, 25, 30] : List (Points 5)).getD x.val 0
def CollH18 : Collineation5 where
  p := CollH18_p
  pinv := CollH18_pi
  l := CollH18_l
  linv := CollH18_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
