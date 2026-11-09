import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF18_p (x : Points 5) : Points 5 := ([18, 22, 5, 14, 29, 24, 8, 10, 27, 17, 6, 11, 25, 16, 21, 12, 28, 15, 23, 9, 26, 19, 20, 7, 13, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF18_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 2, 10, 23, 6, 19, 7, 11, 15, 24, 3, 17, 13, 9, 0, 21, 22, 14, 1, 18, 5, 12, 20, 8, 16, 4, 29] : List (Points 5)).getD x.val 0
def CollF18_l (x : Points 5) : Points 5 := ([25, 26, 30, 27, 28, 9, 0, 21, 17, 13, 4, 12, 20, 8, 16, 19, 6, 23, 10, 2, 14, 18, 22, 1, 5, 24, 15, 11, 7, 3, 29] : List (Points 5)).getD x.val 0
def CollF18_li (x : Points 5) : Points 5 := ([6, 23, 19, 29, 10, 24, 16, 28, 13, 5, 18, 27, 11, 9, 20, 26, 14, 8, 21, 15, 12, 7, 22, 17, 25, 0, 1, 3, 4, 30, 2] : List (Points 5)).getD x.val 0
def CollF18 : Collineation5 where
  p := CollF18_p
  pinv := CollF18_pi
  l := CollF18_l
  linv := CollF18_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
