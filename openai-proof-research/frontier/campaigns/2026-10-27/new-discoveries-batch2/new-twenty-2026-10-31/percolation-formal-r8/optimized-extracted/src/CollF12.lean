import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF12_p (x : Points 5) : Points 5 := ([12, 9, 23, 15, 28, 6, 21, 16, 25, 11, 24, 17, 27, 10, 8, 18, 29, 14, 5, 22, 26, 13, 7, 20, 19, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF12_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 18, 5, 22, 14, 1, 13, 9, 0, 21, 17, 3, 7, 11, 15, 24, 23, 6, 19, 2, 10, 8, 20, 12, 4, 16, 29] : List (Points 5)).getD x.val 0
def CollF12_l (x : Points 5) : Points 5 := ([25, 28, 27, 30, 26, 9, 0, 21, 17, 13, 14, 22, 5, 18, 1, 24, 11, 3, 15, 7, 4, 8, 12, 16, 20, 19, 10, 6, 2, 23, 29] : List (Points 5)).getD x.val 0
def CollF12_li (x : Points 5) : Points 5 := ([6, 14, 28, 17, 20, 12, 27, 19, 21, 5, 26, 16, 22, 9, 10, 18, 23, 8, 13, 25, 24, 7, 11, 29, 15, 0, 4, 2, 1, 30, 3] : List (Points 5)).getD x.val 0
def CollF12 : Collineation5 where
  p := CollF12_p
  pinv := CollF12_pi
  l := CollF12_l
  linv := CollF12_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
