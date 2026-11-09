import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG19_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 22, 5, 14, 29, 18, 11, 21, 25, 6, 16, 8, 27, 24, 10, 17, 28, 12, 9, 23, 15, 19, 20, 7, 13, 26, 1] : List (Points 5)).getD x.val 0
def CollG19_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 6, 13, 27, 15, 22, 18, 10, 21, 28, 7, 24, 14, 19, 9, 25, 26, 11, 5, 23, 17, 12, 29, 16, 20, 8, 4] : List (Points 5)).getD x.val 0
def CollG19_l (x : Points 5) : Points 5 := ([9, 15, 1, 12, 23, 19, 0, 11, 22, 8, 4, 10, 21, 7, 18, 14, 20, 6, 17, 3, 24, 5, 16, 2, 13, 25, 29, 27, 26, 30, 28] : List (Points 5)).getD x.val 0
def CollG19_li (x : Points 5) : Points 5 := ([6, 2, 23, 19, 10, 21, 17, 13, 9, 0, 11, 7, 3, 24, 15, 1, 22, 18, 14, 5, 16, 12, 8, 4, 20, 25, 28, 27, 30, 26, 29] : List (Points 5)).getD x.val 0
def CollG19 : Collineation5 where
  p := CollG19_p
  pinv := CollG19_pi
  l := CollG19_l
  linv := CollG19_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
