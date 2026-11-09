import Collineation
namespace Percolation
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def CollG23_p (x : Points 5) : Points 5 := ([0, 3, 4, 2, 30, 14, 18, 5, 29, 22, 7, 13, 26, 19, 20, 16, 25, 11, 6, 21, 27, 8, 17, 10, 24, 23, 12, 15, 9, 28, 1] : List (Points 5)).getD x.val 0
def CollG23_pi (x : Points 5) : Points 5 := ([0, 30, 3, 1, 2, 7, 18, 10, 21, 28, 23, 17, 26, 11, 5, 27, 15, 22, 6, 13, 14, 19, 9, 25, 24, 16, 12, 20, 29, 8, 4] : List (Points 5)).getD x.val 0
def CollG23_l (x : Points 5) : Points 5 := ([19, 5, 21, 12, 3, 14, 0, 16, 7, 23, 9, 20, 11, 2, 18, 4, 15, 6, 22, 13, 24, 10, 1, 17, 8, 25, 28, 30, 26, 29, 27] : List (Points 5)).getD x.val 0
def CollG23_li (x : Points 5) : Points 5 := ([6, 22, 13, 4, 15, 1, 17, 8, 24, 10, 21, 12, 3, 19, 5, 16, 7, 23, 14, 0, 11, 2, 18, 9, 20, 25, 28, 30, 26, 29, 27] : List (Points 5)).getD x.val 0
def CollG23 : Collineation5 where
  p := CollG23_p
  pinv := CollG23_pi
  l := CollG23_l
  linv := CollG23_li
  pp := by decide
  pi := by decide
  ll := by decide
  li := by decide
  perm := by decide
  incidence_preserved := by decide
end Percolation
