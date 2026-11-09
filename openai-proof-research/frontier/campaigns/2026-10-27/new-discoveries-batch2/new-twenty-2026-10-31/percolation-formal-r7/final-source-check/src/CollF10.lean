import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF10_p (x : Points 5) : Points 5 := ([10, 8, 24, 17, 27, 5, 22, 18, 29, 14, 20, 19, 26, 13, 7, 15, 28, 12, 9, 23, 25, 11, 6, 21, 16, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF10_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 5, 22, 14, 1, 18, 0, 21, 17, 13, 9, 15, 24, 3, 7, 11, 10, 23, 6, 19, 2, 20, 12, 4, 16, 8, 29] : List (Points 5)).getD x.val 0
def CollF10_l (x : Points 5) : Points 5 := ([25, 27, 29, 26, 28, 4, 0, 1, 2, 3, 9, 7, 5, 8, 6, 19, 16, 18, 15, 17, 24, 23, 22, 21, 20, 14, 10, 11, 12, 13, 30] : List (Points 5)).getD x.val 0
def CollF10_li (x : Points 5) : Points 5 := ([6, 7, 8, 9, 5, 12, 14, 11, 13, 10, 26, 27, 28, 29, 25, 18, 16, 19, 17, 15, 24, 23, 22, 21, 20, 0, 3, 1, 4, 2, 30] : List (Points 5)).getD x.val 0
def CollF10 : Collineation5 where
  p := CollF10_p
  pinv := CollF10_pi
  l := CollF10_l
  linv := CollF10_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
