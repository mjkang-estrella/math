import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollF22_p (x : Points 5) : Points 5 := ([22, 14, 18, 5, 29, 11, 16, 6, 25, 21, 19, 7, 26, 20, 13, 8, 27, 24, 10, 17, 28, 23, 12, 15, 9, 0, 3, 4, 2, 30, 1] : List (Points 5)).getD x.val 0
def CollF22_pi (x : Points 5) : Points 5 := ([25, 30, 28, 26, 27, 3, 7, 11, 15, 24, 18, 5, 22, 14, 1, 23, 6, 19, 2, 10, 13, 9, 0, 21, 17, 8, 12, 16, 20, 4, 29] : List (Points 5)).getD x.val 0
def CollF22_l (x : Points 5) : Points 5 := ([25, 26, 29, 30, 27, 19, 0, 11, 22, 8, 9, 12, 15, 23, 1, 14, 6, 3, 20, 17, 4, 18, 7, 21, 10, 24, 5, 16, 2, 13, 28] : List (Points 5)).getD x.val 0
def CollF22_li (x : Points 5) : Points 5 := ([6, 14, 28, 17, 20, 26, 16, 22, 9, 10, 24, 7, 11, 29, 15, 12, 27, 19, 21, 5, 18, 23, 8, 13, 25, 0, 1, 4, 30, 2, 3] : List (Points 5)).getD x.val 0
def CollF22 : Collineation5 where
  p := CollF22_p
  pinv := CollF22_pi
  l := CollF22_l
  linv := CollF22_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
