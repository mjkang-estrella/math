import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG12_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 6, 21, 16, 25, 11, 18, 5, 29, 22, 14, 24, 27, 8, 17, 10, 26, 19, 20, 7, 13, 12, 9, 23, 15, 28, 1] : List (Points 5)).getD x.val 0
def CollG12_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 11, 5, 23, 17, 26, 19, 9, 25, 24, 14, 28, 7, 18, 10, 21, 22, 6, 13, 27, 15, 8, 20, 16, 29, 12, 4] : List (Points 5)).getD x.val 0
def CollG12_l (x : Points 5) : Points 5 := ([19, 10, 6, 2, 23, 9, 0, 21, 17, 13, 24, 15, 11, 7, 3, 14, 5, 1, 22, 18, 4, 20, 16, 12, 8, 25, 28, 27, 30, 26, 29] : List (Points 5)).getD x.val 0
def CollG12_li (x : Points 5) : Points 5 := ([6, 17, 3, 14, 20, 16, 2, 13, 24, 5, 1, 12, 23, 9, 15, 11, 22, 8, 19, 0, 21, 7, 18, 4, 10, 25, 29, 27, 26, 30, 28] : List (Points 5)).getD x.val 0
def CollG12 : Collineation5 where
  p := CollG12_p
  pinv := CollG12_pi
  l := CollG12_l
  linv := CollG12_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
