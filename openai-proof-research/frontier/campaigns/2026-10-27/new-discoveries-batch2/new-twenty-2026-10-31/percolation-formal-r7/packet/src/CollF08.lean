import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF08_p (x : Points 5) : Points 5 := ([8, 17, 10, 24, 27, 19, 13, 20, 26, 7, 11, 21, 25, 6, 16, 22, 29, 5, 18, 14, 28, 9, 15, 12, 23, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF08_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 17, 13, 9, 0, 21, 2, 10, 23, 6, 19, 22, 14, 1, 18, 5, 7, 11, 15, 24, 3, 12, 8, 4, 20, 16, 29] : List (Points 5)).getD x.val 0
def CollF08_l (x : Points 5) : Points 5 := ([25, 27, 30, 29, 26, 19, 0, 11, 22, 8, 4, 7, 10, 18, 21, 24, 16, 13, 5, 2, 9, 23, 12, 1, 15, 14, 20, 6, 17, 3, 28] : List (Points 5)).getD x.val 0
def CollF08_li (x : Points 5) : Points 5 := ([6, 23, 19, 29, 10, 18, 27, 11, 9, 20, 12, 7, 22, 17, 25, 24, 16, 28, 13, 5, 26, 14, 8, 21, 15, 0, 4, 1, 30, 3, 2] : List (Points 5)).getD x.val 0
def CollF08 : Collineation5 where
  p := CollF08_p
  pinv := CollF08_pi
  l := CollF08_l
  linv := CollF08_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
