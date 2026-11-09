import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF05_p (x : Points 5) : Points 5 := ([5, 18, 14, 22, 29, 15, 12, 23, 28, 9, 10, 24, 27, 8, 17, 20, 26, 7, 19, 13, 25, 6, 16, 11, 21, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF05_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 0, 21, 17, 13, 9, 10, 23, 6, 19, 2, 5, 22, 14, 1, 18, 15, 24, 3, 7, 11, 20, 16, 12, 8, 4, 29] : List (Points 5)).getD x.val 0
def CollF05_l (x : Points 5) : Points 5 := ([25, 26, 27, 28, 29, 4, 0, 1, 2, 3, 14, 12, 10, 13, 11, 9, 6, 8, 5, 7, 19, 18, 17, 16, 15, 24, 20, 21, 22, 23, 30] : List (Points 5)).getD x.val 0
def CollF05_li (x : Points 5) : Points 5 := ([6, 7, 8, 9, 5, 18, 16, 19, 17, 15, 12, 14, 11, 13, 10, 24, 23, 22, 21, 20, 26, 27, 28, 29, 25, 0, 1, 2, 3, 4, 30] : List (Points 5)).getD x.val 0
def CollF05 : Collineation5 where
  p := CollF05_p
  pinv := CollF05_pi
  l := CollF05_l
  linv := CollF05_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
