import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF11_p (x : Points 5) : Points 5 := ([11, 6, 21, 16, 25, 8, 24, 17, 27, 10, 22, 18, 29, 14, 5, 19, 26, 13, 7, 20, 28, 12, 9, 23, 15, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF11_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 14, 1, 18, 5, 22, 9, 0, 21, 17, 13, 24, 3, 7, 11, 15, 19, 2, 10, 23, 6, 4, 16, 8, 20, 12, 29] : List (Points 5)).getD x.val 0
def CollF11_l (x : Points 5) : Points 5 := ([25, 30, 26, 27, 29, 19, 0, 11, 22, 8, 24, 2, 5, 13, 16, 9, 1, 23, 15, 12, 14, 3, 17, 6, 20, 4, 10, 21, 7, 18, 28] : List (Points 5)).getD x.val 0
def CollF11_li (x : Points 5) : Points 5 := ([6, 16, 11, 21, 25, 12, 23, 28, 9, 15, 26, 7, 19, 13, 20, 18, 14, 22, 29, 5, 24, 27, 8, 17, 10, 0, 2, 3, 30, 4, 1] : List (Points 5)).getD x.val 0
def CollF11 : Collineation5 where
  p := CollF11_p
  pinv := CollF11_pi
  l := CollF11_l
  linv := CollF11_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
